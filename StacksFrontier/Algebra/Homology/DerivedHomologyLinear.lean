module

public import Mathlib

/-!
# Homology is linear, and the connecting map of the homology sequence is natural

Two facts about the homology of complexes over an `R`-linear abelian category that Mathlib states
only for short complexes, respectively only for a morphism of short exact sequences of cochain
complexes.

The first is linearity of homology in the morphism. Mathlib has
`CategoryTheory.ShortComplex.homologyMap_smul` and leaves the homological-complex version as a
`TODO`; it follows at once, because the short complex attached to a complex in a degree is
`R`-linear in the morphism by construction. Linearity then passes to the derived category: the
homology functor on `DerivedCategory C` lifts the one on `CochainComplex C ℤ` along the
localization functor, and `CategoryTheory.Localization.functor_linear_iff` says a lift of a linear
functor along a linear localization functor is linear.

Linearity is what makes the homology of a complex of modules a module over the base ring in the
expected way: multiplication by a scalar on the complex induces multiplication by that scalar on
homology.

The second is the naturality of `DerivedCategory.HomologySequence.δ` in the triangle. The
connecting map is `Functor.shiftMap` of the third map of the triangle, and `Functor.shiftMap`
absorbs a composition on either side, so the third square of a morphism of triangles turns into
the naturality square for `δ`. Mathlib proves this only for `triangleOfSESδ`, i.e. for triangles
coming from a short exact sequence of cochain complexes; the statement below is for an arbitrary
morphism of triangles.

## Main results

* `Stacks.HomologyLinear.homologyMap_smul` — homology of homological complexes is linear in the
  morphism.
* `Stacks.HomologyLinear.derivedHomologyFunctor_linear` — the homology functor on the derived
  category is linear.
* `Stacks.HomologyLinear.homologySequenceδ_naturality` — the connecting map of the homology
  sequence is natural in the triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe t w v u

namespace Stacks.HomologyLinear

section Linear

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Linear R C] [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι}

/-- **Homology of homological complexes is linear in the morphism.** This is
`CategoryTheory.ShortComplex.homologyMap_smul` transported along the construction of the homology
of a complex in a degree as the homology of a short complex, which is itself linear in the
morphism. -/
theorem homologyMap_smul {K L : HomologicalComplex C c} (φ : K ⟶ L) (a : R) (i : ι) :
    HomologicalComplex.homologyMap (a • φ) i = a • HomologicalComplex.homologyMap φ i :=
  have h : (HomologicalComplex.shortComplexFunctor C c i).map (a • φ) =
      a • (HomologicalComplex.shortComplexFunctor C c i).map φ := by
    apply ShortComplex.Hom.ext <;> rfl
  (congrArg (fun ψ ↦ ShortComplex.homologyMap ψ) h).trans
    (ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor C c i).map φ) a)

/-- The homology functor on homological complexes is linear. -/
instance homologyFunctor_linear (i : ι) :
    Functor.Linear R (HomologicalComplex.homologyFunctor C c i) where
  map_smul {_ _} φ a := homologyMap_smul φ a i

end Linear

section Derived

variable {R : Type t} [Ring R] {C : Type u} [Category.{v} C] [Abelian C]
  [CategoryTheory.Linear R C] [HasDerivedCategory.{w} C]

/-- The homology functor on cochain complexes lifts to the derived category. -/
@[instance_reducible] def liftingHomologyFunctor (n : ℤ) :
    CategoryTheory.Localization.Lifting (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n)
      (DerivedCategory.homologyFunctor C n) :=
  ⟨DerivedCategory.homologyFunctorFactors C n⟩

/-- **The homology functor on the derived category is linear.** It lifts the homology functor on
cochain complexes, which is linear, along the localization functor, which is linear. -/
instance derivedHomologyFunctor_linear (n : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor C n) :=
  letI := liftingHomologyFunctor (C := C) n
  (CategoryTheory.Localization.functor_linear_iff DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) R _ _).1
    (homologyFunctor_linear n)

/-- **Homology on the derived category is linear in the morphism.** -/
theorem derivedHomologyMap_smul (n : ℤ) {X Y : DerivedCategory C} (φ : X ⟶ Y) (a : R) :
    (DerivedCategory.homologyFunctor C n).map (a • φ) =
      a • (DerivedCategory.homologyFunctor C n).map φ :=
  (DerivedCategory.homologyFunctor C n).map_smul a φ

/-- **The connecting map of the homology sequence is natural in the triangle.** For a morphism of
triangles in the derived category the two connecting maps fit into a commutative square with the
maps induced on homology by its first and third components.

The connecting map is `CategoryTheory.Functor.shiftMap` of the third map of the triangle, and
`shiftMap` absorbs a composition on either side, so this is exactly the third square of the
morphism of triangles. -/
theorem homologySequenceδ_naturality {T₁ T₂ : Triangle (DerivedCategory C)} (ψ : T₁ ⟶ T₂)
    (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    DerivedCategory.HomologySequence.δ T₁ n₀ n₁ h ≫
        (DerivedCategory.homologyFunctor C n₁).map ψ.hom₁ =
      (DerivedCategory.homologyFunctor C n₀).map ψ.hom₃ ≫
        DerivedCategory.HomologySequence.δ T₂ n₀ n₁ h :=
  have hn : (1 : ℤ) + n₀ = n₁ := by rw [add_comm 1, h]
  ((DerivedCategory.homologyFunctor C 0).shiftMap_comp T₁.mor₃ ψ.hom₁ n₀ n₁ hn).symm.trans
    ((congrArg (fun x : T₁.obj₃ ⟶ (shiftFunctor (DerivedCategory C) (1 : ℤ)).obj T₂.obj₁ ↦
        (DerivedCategory.homologyFunctor C 0).shiftMap x n₀ n₁ hn) ψ.comm₃).trans
      ((DerivedCategory.homologyFunctor C 0).shiftMap_comp' ψ.hom₃ T₂.mor₃ n₀ n₁ hn))

end Derived

end Stacks.HomologyLinear

end
