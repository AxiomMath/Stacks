module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.LeftFactorTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.RightFactorTriangulated
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring with a fixed complex is a triangulated functor

Part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery`:
Statements 1 and 2 of Lemma 21.17.1 (tag 06YM) and the
general reduction of tag 0G6E for an arbitrary additive bifunctor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

variable [HasBinaryBiproducts (SheafOfModules (ringSheaf R))]

-- Main Statement(s)

-- The zero object of `Mod(O)` comes from `SheafOfModules.instAbelian`, which asks for
-- `HasSheafify` rather than the `HasWeakSheafify` above.  With the sections universe `w`
-- free, Mathlib's global `HasSheafify` instance — whose side condition
-- `[∀ X, Small.{w} (J.Cover X)ᵒᵖ]` is exactly what used to force `w ≥ max u v` — no longer
-- fires, so the hypothesis is recorded here.  At `w := max u v` it is discharged by that
-- instance, which is how the old statements are recovered.
variable [HasSheafify J AddCommGrpCat]

/-- **Statement 1.**  Fix a complex `G^•` of `O`-modules.  The functor
`F^• ↦ Tot(G^• ⊗_O F^•)` on the homotopy category `K(Mod(O))` is an exact functor
of triangulated categories (Definition 5).

Concretely: there is a functor `Φ : K(Mod(O)) ⥤ K(Mod(O))` together with a
functorial isomorphism `ξ` (a `CommShift ℤ` structure, incorporating the Koszul
signs of tag 0FLG) such that
* `Φ` is additive;
* `Φ` lifts the complex-level functor `F^• ↦ Tot(G^• ⊗_O F^•)` through the
  homotopy quotient -- i.e. `quotF ⋙ Φ ≅ leftTensorComplex ⋙ quotF` -- so it is
  well defined on `K(Mod(O))` (sends homotopic maps to homotopic maps); and
* `Φ`, equipped with the commutation-with-shift datum `ξ`, is a triangulated
  functor: it commutes with the shift up to `ξ` and sends distinguished triangles
  to distinguished triangles. -/
@[stacks 06YM "the functor F ↦ Tot(G ⊗_O F), the fixed complex on the left",
  sga "4 XVII 4.1.6" "comm. O, G fixed, left", sga "4½ Etat_0 1.3.3" "special case"]
theorem statement1
    (G : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)) :
    ∃ (Φ : HomotopyCategory (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
            HomotopyCategory (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ))
      (ξ : Φ.CommShift ℤ),
      Φ.Additive ∧
        Nonempty (quotF R ⋙ Φ ≅ leftTensorComplex R G ⋙ quotF R) ∧
          (letI := ξ; Φ.IsTriangulated) :=
  ⟨Reduction.bifunctorPhi (sheafTensor R) G, Reduction.bifunctorXi (sheafTensor R) G,
    inferInstance, ⟨Reduction.bifunctorPhiFactors (sheafTensor R) G⟩,
    Reduction.bifunctorPhi_isTriangulated (sheafTensor R) G⟩

/-- **Statement 2.**  Fix a complex `G^•` of `O`-modules.  The functor
`F^• ↦ Tot(F^• ⊗_O G^•)` on the homotopy category `K(Mod(O))` is an exact functor
of triangulated categories (Definition 5).

Concretely: there is a functor `Φ : K(Mod(O)) ⥤ K(Mod(O))` together with a
functorial isomorphism `ξ` (a `CommShift ℤ` structure, incorporating the Koszul
signs) such that
* `Φ` is additive;
* `Φ` lifts the complex-level functor `F^• ↦ Tot(F^• ⊗_O G^•)` through the
  homotopy quotient -- i.e. `quotF ⋙ Φ ≅ rightTensorComplex ⋙ quotF`; and
* `Φ`, equipped with the commutation-with-shift datum `ξ`, is a triangulated
  functor. -/
@[stacks 06YM "the functor F ↦ Tot(F ⊗_O G), the fixed complex on the right",
  sga "4 XVII 4.1.6" "comm. O, G fixed, right", sga "4½ Etat_0 1.3.3" "special case"]
theorem statement2
    (G : HomologicalComplex (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ)) :
    ∃ (Φ : HomotopyCategory (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ) ⥤
            HomotopyCategory (SheafOfModules (ringSheaf R)) (ComplexShape.up ℤ))
      (ξ : Φ.CommShift ℤ),
      Φ.Additive ∧
        Nonempty (quotF R ⋙ Φ ≅ rightTensorComplex R G ⋙ quotF R) ∧
          (letI := ξ; Φ.IsTriangulated) :=
  ⟨Reduction.bifunctorPhiR (sheafTensor R) G, Reduction.bifunctorXiR (sheafTensor R) G,
    inferInstance, ⟨Reduction.bifunctorPhiRFactors (sheafTensor R) G⟩,
    Reduction.bifunctorPhiR_isTriangulated (sheafTensor R) G⟩

/-- **The general reduction (Derived Categories, Remark 13.10.9 / tag 0G6E).**
For additive categories `A, B, D` with `D` having the countable direct sums
needed to form the relevant total complexes, and any functor `F : A ⥤ B ⥤ D`
additive (bilinear on morphisms) in each variable, fixing one complex variable
`G^•` and taking `Tot` of the resulting double complex yields an exact functor of
homotopy categories `K(B) ⥤ K(D)` (here the fixed complex is the LEFT factor).
Statements 1 and 2 are the instances `A = B = D = Mod(O)`, `F = ⊗_O = sheafTensor`. -/
@[stacks 0G6E "(1)", sga "4 XVII 7.3.3" "special case", sga "4½ Etat_0 1.3.3" "partial"]
theorem bifunctor_homotopy_isTriangulated
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D]
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    ∃ (Φ : HomotopyCategory B (ComplexShape.up ℤ) ⥤ HomotopyCategory D (ComplexShape.up ℤ))
      (ξ : Φ.CommShift ℤ),
      Φ.Additive ∧
        Nonempty (HomotopyCategory.quotient B (ComplexShape.up ℤ) ⋙ Φ ≅
          (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).obj G ⋙
            HomotopyCategory.quotient D (ComplexShape.up ℤ)) ∧
          (letI := ξ; Φ.IsTriangulated) :=
  ⟨Reduction.bifunctorPhi F G, Reduction.bifunctorXi F G, inferInstance,
    ⟨Reduction.bifunctorPhiFactors F G⟩, Reduction.bifunctorPhi_isTriangulated F G⟩

/-- **Stacks 0G6E (2).** The right-variable version of
`bifunctor_homotopy_isTriangulated`: fixing a complex of `B` and totalizing in the `A`
variable gives an exact functor `K(A) ⟶ K(D)`. -/
@[stacks 0G6E "(2)", sga "4 XVII 7.3.3" "special case", sga "4½ Etat_0 1.3.3" "partial"]
theorem bifunctor_homotopy_flip_isTriangulated
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D]
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    ∃ (Φ : HomotopyCategory A (ComplexShape.up ℤ) ⥤
        HomotopyCategory D (ComplexShape.up ℤ))
      (ξ : Φ.CommShift ℤ),
      Φ.Additive ∧
        Nonempty (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ Φ ≅
          (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).flip.obj G ⋙
            HomotopyCategory.quotient D (ComplexShape.up ℤ)) ∧
          (letI := ξ; Φ.IsTriangulated) :=
  ⟨Reduction.bifunctorPhiR F G, Reduction.bifunctorXiR F G, inferInstance,
    ⟨Reduction.bifunctorPhiRFactors F G⟩, Reduction.bifunctorPhiR_isTriangulated F G⟩

end Stacks.SheafOfModules.Tensor

end
