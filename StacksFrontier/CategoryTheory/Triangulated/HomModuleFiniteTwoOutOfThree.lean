module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of `Hom` groups along distinguished triangles

Let `A` be a Noetherian ring and `D` an `A`-linear pretriangulated category.  For an object `O`
and a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]`, the sequence of `A`-modules
`Hom(O, X₁) ⟶ Hom(O, X₂) ⟶ Hom(O, X₃)` is exact, so `Hom(O, X₂)` is a finite `A`-module as soon
as the two outer ones are: it is an extension of a submodule of `Hom(O, X₃)` by a quotient of
`Hom(O, X₁)`.

This is the two-out-of-three step of the dévissages proving finiteness of the groups
`Hom(𝒪, N[n])` and `Ext^n(K, L)` on a proper algebraic space (Stacks 0D0T).

## Main results

* `CategoryTheory.Pretriangulated.moduleFinite_hom_obj₂_of_distinguished`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

variable {A : Type*} [CommRing A] [IsNoetherianRing A] {D : Type*} [Category D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Linear A D]

/-- **Two out of three for finiteness of `Hom(O, -)` along a distinguished triangle.** -/
theorem moduleFinite_hom_obj₂_of_distinguished (O : D) (T : Triangle D)
    (hT : T ∈ distTriang D) (h₁ : Module.Finite A (O ⟶ T.obj₁))
    (h₃ : Module.Finite A (O ⟶ T.obj₃)) : Module.Finite A (O ⟶ T.obj₂) := by
  let f : (O ⟶ T.obj₁) →ₗ[A] (O ⟶ T.obj₂) := Linear.rightComp A O T.mor₁
  let g : (O ⟶ T.obj₂) →ₗ[A] (O ⟶ T.obj₃) := Linear.rightComp A O T.mor₂
  have hfg : LinearMap.range f = LinearMap.ker g := by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mem_ker]
    refine ⟨?_, fun hx => (Triangle.coyoneda_exact₂ T hT x hx).imp fun _ => Eq.symm⟩
    rintro ⟨y, rfl⟩
    simp [f, g, comp_distTriang_mor_zero₁₂ T hT]
  exact Module.Finite.of_exact (f := (LinearMap.range f).subtype) (g := g.rangeRestrict)
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype, hfg]))
    g.surjective_rangeRestrict

end CategoryTheory.Pretriangulated

end
