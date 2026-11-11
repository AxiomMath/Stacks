module

public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.YonedaNondegenerate
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.RingedSpaceTrace
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.DualizingModule
public import StacksFrontier.AlgebraicGeometry.Modules.ExtStructureSheafAbelian

/-!
# Serre duality as a nondegenerate Yoneda pairing of `Ext` groups

Let `X` be a proper Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`,
with dualizing module `ω_X` ([Stacks, Tag 0FVZ]). For a quasi-coherent `𝒪_X`-module `ℰ` and
`i + j = d`, the Yoneda product

`Extʲ(𝒪_X, ℰ) × Extⁱ(ℰ, ω_X) ⟶ Extᵈ(𝒪_X, ω_X)`

is nondegenerate in the first variable: a nonzero `y ∈ Extʲ(𝒪_X, ℰ) = Hʲ(X, ℰ)` has
`y ∘ β ≠ 0` for some `β`. This is `Stacks.Duality.exists_comp_ne_zero_of_ne_zero` for
`M = ℰ[j]`, read through `ω_X^• ≅ ω_X[d]`.

## Main results

* `Stacks.Duality.exists_ext_comp_ne_zero_of_ne_zero`.

## References

* [Stacks Project, Tag 0FVZ](https://stacks.math.columbia.edu/tag/0FVZ)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- `𝒪_X[0]` in the two presentations used by `homToHomology` and by `Ext`. -/
def structureSheafSingleIso :
    (DerivedCategory.singleFunctor X.Modules 0).obj (Scheme.Modules.unitModule X) ≅
      structureSheafSingle (X := X) :=
  (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app _ ≪≫
    ((DerivedCategory.quotientCompQhIso X.Modules).app _).symm

/-- `ℰ[j]` lies in `D_QCoh(𝒪_X)` for `ℰ` quasi-coherent. -/
abbrev shiftedSingleQuasiCoherent (E : X.Modules) [E.IsQuasicoherent] (j : ℤ) :
    quasiCoherentDerivedCategory X :=
  ⟨((DerivedCategory.singleFunctor X.Modules 0).obj E)⟦j⟧, fun n =>
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (((DerivedCategory.homologyFunctor X.Modules 0).shiftIso j n (j + n) rfl).app _).symm
      ((singleQuasiCoherentDegreeZero E).property (j + n))⟩

/-- **Serre duality as a nondegenerate Yoneda pairing.** Let `X` be proper, Cohen--Macaulay and
equidimensional of dimension `d` over a field, `ℰ` quasi-coherent and `i + j = d`. Every nonzero
`y ∈ Extʲ(𝒪_X, ℰ)` has some `β ∈ Extⁱ(ℰ, ω_X)` with `y ∘ β ≠ 0` in `Extᵈ(𝒪_X, ω_X)`. -/
theorem exists_ext_comp_ne_zero_of_ne_zero (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    (E : X.Modules) [E.IsQuasicoherent] (i j : ℕ) (hij : j + i = d)
    (y : Ext.{u} (Scheme.Modules.unitModule X) E j) (hy : y ≠ 0) :
    ∃ β : Ext.{u} E (dualizingModule f) i, y.comp β hij ≠ 0 := by
  let M := shiftedSingleQuasiCoherent E (j : ℤ)
  let ŷ : structureSheafSingle (X := X) ⟶ M.obj := (structureSheafSingleIso (X := X)).inv ≫ y.hom
  have hŷ : ŷ ≠ 0 := by
    intro h
    apply hy
    have h' : ((structureSheafSingleIso (X := X)).hom ≫ ŷ) = 0 := by rw [h, Limits.comp_zero]
    have h'' : (y.hom : (DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Modules.unitModule X) ⟶ M.obj) = 0 := by
      simpa [ŷ] using h'
    apply Ext.ext
    rw [Ext.zero_hom]
    exact h''
  obtain ⟨α, hα⟩ := exists_comp_ne_zero_of_ne_zero f M ŷ hŷ
  -- `α` read as a morphism `ℰ[j] ⟶ ω_X[d]`
  let α' : M.obj ⟶ ((DerivedCategory.singleFunctor X.Modules 0).obj (dualizingModule f))⟦(d : ℤ)⟧ :=
    α ≫ (shiftFunctorZero (DerivedCategory X.Modules) ℤ).hom.app _ ≫
      (relativeDualizingComplexIsoShiftOfIsProper f hCM hequi d hd).hom
  have hα' : ŷ ≫ α' ≠ 0 := by
    intro h
    apply hα
    have := congrArg (· ≫ (relativeDualizingComplexIsoShiftOfIsProper f hCM hequi d hd).inv ≫
      (shiftFunctorZero (DerivedCategory X.Modules) ℤ).inv.app _) h
    simpa [α'] using this
  -- `α' = βh⟦j⟧ ≫ (shiftFunctorAdd' i j d).inv` for some `βh : ℰ[0] ⟶ ω_X[i]`
  obtain ⟨βh, hβh⟩ := (shiftFunctor (DerivedCategory X.Modules) (j : ℤ)).map_surjective
    (α' ≫ (shiftFunctorAdd' (DerivedCategory X.Modules) (i : ℤ) (j : ℤ) (d : ℤ)
      (by omega)).hom.app _)
  refine ⟨Ext.homEquiv.symm βh, fun h0 => hα' ?_⟩
  have h1 : (y.comp (Ext.homEquiv.symm βh) hij).hom = 0 := by rw [h0]; simp
  rw [Ext.comp_hom] at h1
  have h2 : y.hom ≫ βh⟦(j : ℤ)⟧' ≫ (shiftFunctorAdd' (DerivedCategory X.Modules) (i : ℤ) (j : ℤ)
      (d : ℤ) (by omega)).inv.app _ = 0 := by
    have := h1
    simp only [Ext.hom, Equiv.apply_symm_apply] at this
    exact this
  rw [hβh] at h2
  have h3 : y.hom ≫ α' = 0 := by
    have e : (α' ≫ (shiftFunctorAdd' (DerivedCategory X.Modules) (i : ℤ) (j : ℤ) (d : ℤ)
        (by omega)).hom.app _) ≫ (shiftFunctorAdd' (DerivedCategory X.Modules) (i : ℤ) (j : ℤ)
        (d : ℤ) (by omega)).inv.app _ = α' :=
      (Category.assoc _ _ _).trans ((congrArg (α' ≫ ·) (Iso.hom_inv_id_app _ _)).trans
        (Category.comp_id _))
    exact (congrArg (y.hom ≫ ·) e).symm.trans h2
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).trans Limits.comp_zero)

end Stacks.Duality

end
