module

public import StacksFrontier.Deformation.ToposThickening.SquareZeroDerivedObstruction
public import StacksFrontier.Deformation.ToposThickening.SquareZeroLiftRealization

/-!
# Lifts of a bounded above complex across a square-zero thickening: Stacks 0DIZ

Let `C` be a site and `f : O ⟶ O₀` a surjection of sheaves of commutative rings whose kernel `I`
has square zero. Let `K₀ ∈ D⁻(O₀)`. A lift of `K₀` is a pair `(K, α)` of `K ∈ D⁻(O)` and an
isomorphism `α : K ⊗^L_O O₀ ≅ K₀`. Part (2) of Stacks 0DIZ says that, if there is a lift, the
set of isomorphism classes of lifts is principal homogeneous under
`Ext¹_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`.

The action is the one of the proof of the source: for two lifts `(K', α')` and `(K'', α'')`,
the class `ξ` carries `(K', α')` to `(K'', α'')` exactly when `ξ` is the obstruction
`o(α'' ∘ α'⁻¹)` of Stacks 0DIY to lifting the comparison of the two identifications with `K₀`,
read in `Ext¹_{O₀}(K₀, K₀ ⊗^L I)` (`Deformation.ComplexLift.liftDifference`). The obstruction is
taken for the reduction triangle `K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)[1]` computed, as in
the source, by tensoring `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0` with a flat (cellular) resolution of `K`
(`Deformation.ComplexLift.squareZeroFlatReduction`).

The two halves of the proof are
`Deformation.ComplexLift.connectingClass_sub_flatReduction` (two lifts have connecting classes
differing by a restricted class, which makes the map to `Ext¹` injective and additive) and
`Deformation.ComplexLift.exists_connectingClass_sub_flatReduction_eq` (the realization of every
class by the complex `H` of the source).

## Main results

* `Deformation.ComplexLift.squareZeroFlatLiftAutEquiv`: **Stacks 0DIZ (1)**, the automorphisms
  of a lift are the cokernel of `squareZeroFlatLiftBoundary`.
* `Deformation.ComplexLift.exists_addTorsor_squareZeroLifts`: **Stacks 0DIZ (2)**.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}} (f : O ⟶ O₀)
  (hf : Presheaf.IsLocallySurjective J f.hom)
  (hsq : ∀ (U : Cᵒᵖ) (a b : O.obj.obj U), f.hom.app U a = 0 → f.hom.app U b = 0 → a * b = 0)
variable
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]
variable
  {K₀ : DerivedCategory.Minus (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))}

/-- The reduction triangle `K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)[1]` of the square-zero
surjection `f`, computed by tensoring the short exact sequence `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0` with a flat
cellular resolution of `K`, as in the proof of Stacks 0DIZ. -/
def squareZeroFlatReduction :
    DerivedReduction (derivedExtensionOfScalarsData.{d, d₀} f)
      (derivedTensorRight.{d₀} (squareZeroIdeal f hf hsq)) :=
  flatReduction.{d, d₀} f (squareZeroIdealInclusion f hf hsq)
    (squareZeroIdealInclusion_comp f hf hsq) (shortExact_squareZeroIdealSequence f hf hsq)

/-- **Stacks 0DIZ (1), the map.** For a lift `(K, α)` of `K₀ ∈ D⁻(O₀)` across the square-zero
surjection `f`, the canonical map

`Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`

whose cokernel the automorphism group of `(K, α)` is: the connecting map of the reduction
triangle `K ⊗^L_O I ⟶ K ⟶ K ⊗^L_O O₀ ⟶ (K ⊗^L_O I)⟦1⟧` of `f` (computed by a flat resolution),
read through the adjunction between derived base change and restriction of scalars and
through `α`. -/
@[stacks 0DIZ "(1), the map Ext⁻¹(K₀, K₀) → Hom(K₀, K₀ ⊗^L I)"]
def squareZeroFlatLiftBoundary (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    (K₀.obj ⟶ K₀.obj⟦(-1 : ℤ)⟧) →+
      (K₀.obj ⟶ (derivedTensorRight.{d₀} (squareZeroIdeal f hf hsq)).obj K₀.obj) :=
  boundary (squareZeroFlatReduction.{d, d₀} f hf hsq) L

/-- **Stacks 0DIZ (1).** Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a
site whose kernel `I` is an ideal of square zero, let `K₀ ∈ D⁻(O₀)` and let `(K, α)` be a lift
of `K₀`, i.e. `K ∈ D⁻(O)` with `α : K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`. Then the group of
automorphisms of the pair `(K, α)` is canonically the cokernel of the map
`Ext⁻¹_{O₀}(K₀, K₀) ⟶ Hom_{O₀}(K₀, K₀ ⊗^L_{O₀} I)` of
`Deformation.ComplexLift.squareZeroFlatLiftBoundary`. -/
@[stacks 0DIZ "(1)"]
def squareZeroFlatLiftAutEquiv (L : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀) :
    Multiplicative (K₀.obj ⟶
        (derivedTensorRight.{d₀} (squareZeroIdeal f hf hsq)).obj K₀.obj) ⧸
        AddSubgroup.toSubgroup (squareZeroFlatLiftBoundary.{d, d₀} f hf hsq L).range ≃*
      automorphismsOfLift (derivedExtensionOfScalarsData.{d, d₀} f) L :=
  automorphismsOfLiftMulEquiv (squareZeroFlatReduction.{d, d₀} f hf hsq) L

/-- **Stacks 0DIZ (2).** Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a
site whose kernel `I` is an ideal of square zero, and let `K₀ ∈ D⁻(O₀)`. If `K₀` has a lift
`(K, α)`, `K ∈ D⁻(O)`, `α : K ⊗^L_O O₀ ≅ K₀`, then the set of isomorphism classes of lifts of
`K₀` is principal homogeneous under `Ext¹_{O₀}(K₀, K₀ ⊗^L_{O₀} I)`: there is a free and
transitive action of that group on it under which `ξ` carries the class of `(K', α')` to the
class of `(K'', α'')` exactly when `ξ` is the obstruction class of Stacks 0DIY of the comparison
`α'' ∘ α'⁻¹` of the two lifts. -/
@[stacks 0DIZ "(2)"]
theorem exists_addTorsor_squareZeroLifts
    [Nonempty (DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀)] :
    ∃ τ : AddTorsor (K₀.obj ⟶
        ((derivedTensorRight.{d₀} (squareZeroIdeal f hf hsq)).obj K₀.obj)⟦(1 : ℤ)⟧)
        (Quotient (DerivedLift.setoid (T := derivedExtensionOfScalarsData.{d, d₀} f) (K₀ := K₀))),
      ∀ (ξ : K₀.obj ⟶ ((derivedTensorRight.{d₀} (squareZeroIdeal f hf hsq)).obj K₀.obj)⟦(1 : ℤ)⟧)
        (L' L'' : DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) K₀),
        τ.vadd ξ ⟦L'⟧ = ⟦L''⟧ ↔
          liftDifference (squareZeroFlatReduction.{d, d₀} f hf hsq) L'' L' = ξ :=
  exists_addTorsor_liftClasses (squareZeroFlatReduction.{d, d₀} f hf hsq)
    (connectingClass_sub_flatReduction.{d, d₀} (squareZeroIdealInclusion f hf hsq)
      (squareZeroIdealInclusion_comp f hf hsq) (isLocallySurjective_ringSheafMapOf f hf)
      (shortExact_squareZeroIdealSequence f hf hsq))
    (exists_connectingClass_sub_flatReduction_eq.{d, d₀} (squareZeroIdealInclusion f hf hsq)
      (squareZeroIdealInclusion_comp f hf hsq) (shortExact_squareZeroIdealSequence f hf hsq)
      (isLocallySurjective_ringSheafMapOf f hf))

end Deformation.ComplexLift

end
