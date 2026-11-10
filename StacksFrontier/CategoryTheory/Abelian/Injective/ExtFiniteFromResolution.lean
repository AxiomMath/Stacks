module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness of `Ext` from the cohomology of `Hom` into an injective resolution

Let `C` be an `A`-linear abelian category and `R` an injective resolution of an object `Y`.
For every object `X`, every class in `Ext^n(X, Y)` is represented by a morphism
`X ⟶ R^n` killed by the differential, and the morphisms of the form `X ⟶ R^{n-1} ⟶ R^n` represent
zero.  So `Ext^n(X, Y)` is an `A`-linear quotient of the degree-`n` cohomology of the complex
of `A`-modules `Hom(X, R^•)`; in particular it is a finite `A`-module as soon as that
cohomology is.

This is how the finiteness of the cohomology of coherent modules on a proper algebraic space
(Stacks 08AS), which is the cohomology of `Γ(R^•) = Hom(𝒪, R^•)`, gives the finiteness of the
groups `Hom(𝒪, F[n])` of the derived category, as needed in the proof of Stacks 0D0T.

## Main results

* `CategoryTheory.InjectiveResolution.moduleFinite_ext_of_moduleFinite_homology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Abelian Opposite

universe w v u

namespace CategoryTheory.InjectiveResolution

variable {A : Type*} [CommRing A] {C : Type u} [Category.{v} C] [Abelian C] [Linear A C]
  [HasExt.{w} C] {X Y : C} (R : InjectiveResolution Y)

/-- **`Ext^n(X, Y)` is an `A`-linear quotient of the cohomology of `Hom(X, R^•)`**: it is
finite over `A` as soon as that cohomology is. -/
theorem moduleFinite_ext_of_moduleFinite_homology (n : ℕ)
    (hfin : Module.Finite A (((((linearCoyoneda A C).obj (op X)).mapHomologicalComplex _).obj
      R.cocomplex).homology n)) :
    Module.Finite A (Ext X Y n) := by
  let K := (((linearCoyoneda A C).obj (op X)).mapHomologicalComplex _).obj R.cocomplex
  let i := (ComplexShape.up ℕ).prev n
  let S := K.sc' i n (n + 1)
  have hfin' : Module.Finite A S.moduleCatLeftHomologyData.H :=
    Module.Finite.equiv ((K.homologyIsoSc' i n (n + 1) rfl
      ((ComplexShape.up ℕ).next_eq' rfl)) ≪≫ S.moduleCatHomologyIso).toLinearEquiv
  let ψ : LinearMap.ker S.g.hom →ₗ[A] Ext X Y n :=
    { toFun := fun f => R.extMk f.1 (n + 1) rfl f.2
      map_add' := fun f g => (R.add_extMk f.1 g.1 (n + 1) rfl f.2 g.2).symm
      map_smul' := fun a f => by
        let f₁ : X ⟶ R.cocomplex.X n := f.1
        have h := R.mk₀_comp_extMk f₁ (n + 1) rfl f.2 (a • 𝟙 X)
        rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] at h
        refine Eq.trans ?_ h.symm
        congr 1
        exact (by simp : a • f₁ = (a • 𝟙 X) ≫ f₁) }
  have hψ : LinearMap.range S.moduleCatToCycles ≤ LinearMap.ker ψ := by
    rintro _ ⟨g, rfl⟩
    rw [LinearMap.mem_ker]
    let g₁ : X ⟶ R.cocomplex.X i := g
    have hg₁ : (g₁ ≫ R.cocomplex.d i n) ≫ R.cocomplex.d n (n + 1) = 0 := by simp
    change R.extMk (g₁ ≫ R.cocomplex.d i n) (n + 1) rfl hg₁ = 0
    by_cases hin : (ComplexShape.up ℕ).Rel i n
    · exact (R.extMk_eq_zero_iff _ (n + 1) rfl hg₁ i hin).2 ⟨g₁, rfl⟩
    · simp [R.cocomplex.shape i n hin]
  let φ : S.moduleCatLeftHomologyData.H →ₗ[A] Ext X Y n :=
    (LinearMap.range S.moduleCatToCycles).liftQ ψ hψ
  refine Module.Finite.of_surjective φ fun x => ?_
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  exact ⟨Submodule.Quotient.mk ⟨f, hf⟩, rfl⟩

end CategoryTheory.InjectiveResolution

end
