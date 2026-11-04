module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Triangulated.Elementary
public import StacksFrontier.Cotangent.AnyResolutionQuasiIso
public import StacksFrontier.Cotangent.BaseChangeQuasiIso
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

/-!
# Tensor products and the cotangent complex

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras. The cotangent complexes of
the ring maps `R → A`, `R → B`, `R → A ⊗_R B`, `A → A ⊗_R B` and `B → A ⊗_R B` fit into a
`3 × 3` diagram in `D(A ⊗_R B)`:

```
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}      ⟶ E
            ‖                     ↑                ↑
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}      ⟶ L_{A ⊗_R B/A}
                                  ↑                ↑
                      L_{B/R} ⊗^L_B (A ⊗_R B) ═ L_{B/R} ⊗^L_B (A ⊗_R B)
```

Its middle row is the fundamental triangle of `R → A → A ⊗_R B` and its middle column is the
fundamental triangle of `R → B → A ⊗_R B`; the object `E` in the upper right corner is a cone of
`L_{A/R} ⊗^L_A (A ⊗_R B) ⊕ L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}`, and it makes the top row
and the right column distinguished triangles as well.

When `A` and `B` are Tor independent over `R` the object `E` vanishes; that is Tag 09DA, proved
in `StacksFrontier.Cotangent.TensorProductTorIndependent`.

## Main definitions

* `CommAlgCat.cotangentComplexDerived`: the cotangent complex `L_{B/A}` as an object of `D(B)`.
* `CommAlgCat.cotangentComplexDerivedBaseChange`: its derived base change `L_{B/A} ⊗^L_B C`
  along a `B`-algebra `C`.
* `CommAlgCat.cotangentComplexDerivedBaseChangeTermwiseIso`: the identification of
  `L_{B/A} ⊗^L_B C` with the degreewise extension of scalars of `L_{B/A}`.
* `CommAlgCat.cotangentTensorProductBaseChangeMap`: the canonical map
  `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}`, the top row of the diagram.
* `CommAlgCat.TensorProductNineDiagram`: the data of Equation 92.15.0.1, with `E` as a field.

## Main results

* `CommAlgCat.exists_tensorProduct_nine_diagram`: **Stacks 09D9**, the displayed diagram.
* `CommAlgCat.exists_tensorProductNineDiagram`: the same, packaged in
  `CommAlgCat.TensorProductNineDiagram`.
* `CommAlgCat.isIso_cotangentTensorProductBaseChangeMap`: Tag 08QQ at the square
  `R → A`, `R → B`, `A → A ⊗_R B`, `B → A ⊗_R B`, for Tor independent `A` and `B`.

## Implementation notes

The middle row and the middle column of the diagram are taken as parameters, in the shape
Proposition 08QX gives them, and what is proved is the content proper to Equation 92.15.0.1 —
that the two of them extend to the displayed `3 × 3` diagram. The last two conclusions record
the remaining two squares of the nine diagram, namely that the connecting morphisms of the top
row and of the right column recover those of the two given triangles.

Those parameters are not an undischarged assumption: Proposition 08QX is proved, as
`CommAlgCat.productFundamentalTriangle_distinguished` of
`StacksFrontier/Cotangent/Triangle/ProductDescent.lean`, for arbitrary ring maps. They are
parameters *here* because this file sits upstream of that proof — the display's vertices are
named in `StacksFrontier/Cotangent/Triangle/FundamentalDisplay.lean`, which imports this file, and
`ProductDescent` imports that — so neither the triangles nor their morphisms can be referred to
by name in this module. Any consumer that lives downstream of `ProductDescent` instantiates both
from the proposition.

The derived base change `- ⊗^L_B C` is the unbounded derived extension-of-scalars functor of
`StacksFrontier.Homology.Tor.DerivedExtensionScalars`, and the derived categories are the standard
model, as elsewhere in the cotangent-complex files.

## References

* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 09DA](https://stacks.math.columbia.edu/tag/09DA)
* [Stacks Project, Tag 08QQ](https://stacks.math.columbia.edu/tag/08QQ)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08QX](https://stacks.math.columbia.edu/tag/08QX)
* [Stacks Project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0), the nine diagram of a
  commutative square in a triangulated category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

universe u v w w₁ w₂

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- The cotangent complex `L_{B/A}` of a ring map `A → B`, as an object of the derived category
of `B`-modules. -/
noncomputable abbrev cotangentComplexDerived (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) [HasDerivedCategory.{w} (ModuleCat.{max u v} B)] :
    DerivedCategory (ModuleCat.{max u v} B) :=
  DerivedCategory.Q.obj (cotangentComplex A B)

/-- The derived base change `L_{B/A} ⊗^L_B C` of the cotangent complex of `A → B` along a
`B`-algebra `C`, as an object of the derived category of `C`-modules. -/
noncomputable abbrev cotangentComplexDerivedBaseChange (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) (C : Type (max u v)) [CommRing C] [Algebra B C]
    [HasDerivedCategory.{w₁} (ModuleCat.{max u v} B)]
    [HasDerivedCategory.{w₂} (ModuleCat.{max u v} C)] :
    DerivedCategory (ModuleCat.{max u v} C) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    (algebraMap B C)).functor.obj (cotangentComplexDerived A B)

variable (R : Type u) [CommRing R] (A B : Type (max u v)) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- **Stacks 09D9**, Equation 92.15.0.1. Let `A` and `B` be algebras over a ring `R`. Given the
fundamental triangle `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/A}` of
`R → A → A ⊗_R B` and the fundamental triangle
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/B}` of `R → B → A ⊗_R B`, there is an
object `E` of `D(A ⊗_R B)` fitting into the upper right corner of the diagram

```
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}      ⟶ E
            ‖                     ↑                ↑
L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}      ⟶ L_{A ⊗_R B/A}
                                  ↑                ↑
                      L_{B/R} ⊗^L_B (A ⊗_R B) ═ L_{B/R} ⊗^L_B (A ⊗_R B)
```

whose top row and right column are distinguished triangles and whose squares commute. -/
@[stacks 09D9]
theorem exists_tensorProduct_nine_diagram
    {u : cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
    {p : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
      cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B))}
    {d₁ : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶
      (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧}
    (h₁ : Triangle.mk u p d₁ ∈ distTriang _)
    {v : cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
    {q : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
      cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B))}
    {d₂ : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶
      (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
    (h₂ : Triangle.mk v q d₂ ∈ distTriang _) :
    ∃ (E : DerivedCategory (ModuleCat.{max u v} (A ⊗[R] B)))
      (a : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶ E)
      (b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E)
      (e₁ : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧)
      (e₂ : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧),
      Triangle.mk (u ≫ q) a e₁ ∈ distTriang _ ∧
      Triangle.mk (v ≫ p) b e₂ ∈ distTriang _ ∧
      q ≫ a = p ≫ b ∧ b ≫ e₁ = d₁ ∧ a ≫ e₂ = d₂ := by
  have hA := contractible_distinguished₁
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))
  have hB := contractible_distinguished₁
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))
  obtain ⟨E, w₁, w₂, w₃, c₁, c₂, c₃, hw, hc, hc₁, -, hw₁, hsq, hd, -, he, -⟩ :=
    CategoryTheory.Triangulated.exists_nine_diagram hB h₁ hA h₂ (by simp)
  have hc₁' : c₁ = v ≫ p := by simpa using hc₁
  have hw₁' : w₁ = u ≫ q := by simpa using hw₁.symm
  refine ⟨E, w₂, c₂, w₃, c₃, ?_, ?_, hsq.symm, ?_, ?_⟩
  · rw [← hw₁']; exact hw
  · rw [← hc₁']; exact hc
  · simpa using hd.symm
  · simpa using he

/-! ### The derived base change of a cotangent complex is computed degreewise -/

section Termwise

variable (A : Type u) [CommRing A] (Bb : CommAlgCat.{u} A)

/-- The cotangent complex lives in non-positive cohomological degrees. -/
theorem cotangentComplex_isStrictlyLE_zero :
    (cotangentComplex.{u, u} A Bb).IsStrictlyLE 0 :=
  (CochainComplex.isStrictlyLE_iff _ 0).2 fun i hi => cotangentComplex_isZero_pos _ _ i hi

open Opposite Simplicial in
/-- Every term of the cotangent complex `L_{Bb/A}` is a projective `Bb`-module: it is the
extension of scalars along the augmentation of the module of differentials of a polynomial
algebra, which is free. -/
theorem projective_cotangentComplex_X (i : ℤ) :
    Projective ((cotangentComplex.{u, u} A Bb).X i) := by
  rcases lt_or_ge 0 i with hi | hi
  · exact (cotangentComplex_isZero_pos A Bb i hi).projective
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨i.natAbs, by lia⟩
    refine Projective.of_iso (cotangentComplex_degreeIso A Bb n).symm ?_
    have h : (ModuleCat.extendScalars.{u, u, u}
        (standardResolutionAugmentationHom.{u, u} A Bb
          (op ⦋n⦌))).PreservesProjectiveObjects :=
      Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
        (ModuleCat.extendRestrictScalarsAdj _)
    have hfree := free_kaehlerDifferential_standardResolution.{u} A Bb (op ⦋n⦌)
    have : Projective (ModuleCat.of
        ((standardResolution.{u, u} A Bb).left.obj (op ⦋n⦌) : Type u)
        (KaehlerDifferential A
          ((standardResolution.{u, u} A Bb).left.obj (op ⦋n⦌)))) := by
      infer_instance
    exact inferInstanceAs (Projective ((ModuleCat.extendScalars _).obj _))

attribute [local instance] cotangentComplex_isStrictlyLE_zero projective_cotangentComplex_X

variable (C : Type u) [CommRing C] [Algebra Bb C]

/-- The comparison from the derived to the degreewise extension of scalars is invertible on the
cotangent complex, which is a bounded-above complex of projectives. -/
theorem isIso_comparison_app_cotangentComplex :
    IsIso ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
      (algebraMap Bb C)).comparison.app (cotangentComplex.{u, u} A Bb)) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars
    (algebraMap Bb C)).comparison_isIso_of_projective (cotangentComplex.{u, u} A Bb) 0

/-- **`L_{Bb/A} ⊗^L_{Bb} C` is computed by the degreewise extension of scalars.** The terms of
`L_{Bb/A}` are projective `Bb`-modules, so the comparison from the derived base change to the
complex `C ⊗_{Bb} L_{Bb/A}` is an isomorphism in `D(C)`. -/
def cotangentComplexDerivedBaseChangeTermwiseIso :
    cotangentComplexDerivedBaseChange.{u, u} A Bb C ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap Bb C)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (cotangentComplex.{u, u} A Bb)) :=
  have h := isIso_comparison_app_cotangentComplex A Bb C
  @asIso _ _ _ _ _ h

end Termwise

/-! ### Tor independent algebras -/

section TorIndependent

variable (R : Type u) [CommRing R] (A B : Type u) [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- The inclusion `A ⟶ A ⊗_R B`, `a ↦ a ⊗ 1`, as a morphism of `R`-algebras from `A` to
`A ⊗_R B` viewed as a `B`-algebra. -/
def tensorProductIncludeLeft :
    ↥(CommAlgCat.of R A) →ₐ[R] ↥(CommAlgCat.of B (A ⊗[R] B)) :=
  IsScalarTower.toAlgHom R A (A ⊗[R] B)

/-- **The top row of Equation 92.15.0.1.** The canonical morphism
`L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}`: the functoriality map of Tag 08PN for the square
`R → A`, `R → B`, `A → A ⊗_R B`, `B → A ⊗_R B`, read through the identification of the derived
base change with the degreewise one. -/
def cotangentTensorProductBaseChangeMap :
    cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B) ⟶
      cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) :=
  (cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R A) (A ⊗[R] B)).hom ≫
    DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (tensorProductIncludeLeft R A B))

/-- **Tag 08QQ at the tensor-product square.** If `A` and `B` are Tor independent over `R`, the
canonical morphism `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/B}` is an isomorphism: the square
`R → A`, `R → B`, `A → A ⊗_R B`, `B → A ⊗_R B` induces `A ⊗^L_R B = A ⊗_R B`. Remark 08QI, that
the cotangent complex is computed by any resolution, is
`CommAlgCat.cotangentComputedByEveryResolution`. -/
theorem isIso_cotangentTensorProductBaseChangeMap
    (hTor : RingTheory.TorIndependence.TorIndependent R B A) :
    IsIso (cotangentTensorProductBaseChangeMap R A B) := by
  have hQI := cotangentComputedByEveryResolution B (CommAlgCat.of B (A ⊗[R] B))
  have hpush : Function.Bijective (baseChangeUnit (tensorProductIncludeLeft R A B)) :=
    bijective_baseChangeUnit_of_isPushout _ fun _ => rfl
  have h := isIso_Q_map_cotangentExtendScalarsComplexMap
    (tensorProductIncludeLeft R A B) hTor hpush hQI
  show IsIso
    ((cotangentComplexDerivedBaseChangeTermwiseIso R (CommAlgCat.of R A) (A ⊗[R] B)).hom ≫
      DerivedCategory.Q.map (cotangentExtendScalarsComplexMap (tensorProductIncludeLeft R A B)))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h

/-- **The data of Equation 92.15.0.1**, for `R`-algebras `A` and `B` in one universe: the
fundamental triangle of `R → A → A ⊗_R B`, the fundamental triangle of `R → B → A ⊗_R B`, and
the object `E` in the upper right corner together with the two morphisms into it, the two
morphisms out of it, and the identities making the top row and the right column distinguished
triangles and all four squares commute. -/
structure TensorProductNineDiagram where
  /-- The map `L_{A/R} ⊗^L_A (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` of the middle row. -/
  mapA : cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B) ⟶
    cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))
  /-- The map `L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/A}` of the middle row. -/
  projA : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
    cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B))
  /-- The connecting map of the middle row. -/
  shiftA : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧
  /-- The middle row is the fundamental triangle of `R → A → A ⊗_R B`. -/
  rowDistinguished : Triangle.mk mapA projA shiftA ∈ distTriang _
  /-- The map `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/R}` of the middle column. -/
  mapB : cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
    cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))
  /-- The map `L_{A ⊗_R B/R} ⟶ L_{A ⊗_R B/B}` of the middle column. -/
  projB : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
    cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B))
  /-- The connecting map of the middle column. -/
  shiftB : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧
  /-- The middle column is the fundamental triangle of `R → B → A ⊗_R B`. -/
  columnDistinguished : Triangle.mk mapB projB shiftB ∈ distTriang _
  /-- The object `E` in the upper right corner of the diagram. -/
  upperRight : DerivedCategory (ModuleCat.{u} (A ⊗[R] B))
  /-- The map `L_{A ⊗_R B/B} ⟶ E` completing the top row. -/
  fromB : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶ upperRight
  /-- The map `L_{A ⊗_R B/A} ⟶ E` completing the right column. -/
  fromA : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ upperRight
  /-- The connecting map of the top row. -/
  toShiftA : upperRight ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧
  /-- The connecting map of the right column. -/
  toShiftB : upperRight ⟶
    (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧
  /-- The top row is a distinguished triangle. -/
  topRowDistinguished : Triangle.mk (mapA ≫ projB) fromB toShiftA ∈ distTriang _
  /-- The right column is a distinguished triangle. -/
  rightColumnDistinguished : Triangle.mk (mapB ≫ projA) fromA toShiftB ∈ distTriang _
  /-- The upper right square commutes. -/
  comm : projB ≫ fromB = projA ≫ fromA
  /-- The connecting map of the top row recovers that of the middle row. -/
  fromA_comp_toShiftA : fromA ≫ toShiftA = shiftA
  /-- The connecting map of the right column recovers that of the middle column. -/
  fromB_comp_toShiftB : fromB ≫ toShiftB = shiftB

/-- **Stacks 09D9 packaged as `CommAlgCat.TensorProductNineDiagram`.** The two fundamental
triangles of `R → A → A ⊗_R B` and of `R → B → A ⊗_R B` extend to the nine diagram of Equation
92.15.0.1, keeping the two given triangles as its middle row and middle column. -/
theorem exists_tensorProductNineDiagram
    {u : cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
    {p : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
      cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B))}
    {d₁ : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶
      (cotangentComplexDerivedBaseChange R (CommAlgCat.of R A) (A ⊗[R] B))⟦(1 : ℤ)⟧}
    (h₁ : Triangle.mk u p d₁ ∈ distTriang _)
    {v : cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B) ⟶
      cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B))}
    {q : cotangentComplexDerived R (CommAlgCat.of R (A ⊗[R] B)) ⟶
      cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B))}
    {d₂ : cotangentComplexDerived B (CommAlgCat.of B (A ⊗[R] B)) ⟶
      (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}
    (h₂ : Triangle.mk v q d₂ ∈ distTriang _) :
    ∃ D : TensorProductNineDiagram R A B, D.mapA = u ∧ D.projA = p ∧ D.shiftA = d₁ ∧
      D.mapB = v ∧ D.projB = q ∧ D.shiftB = d₂ := by
  obtain ⟨E, a, c, e₁, e₂, ht, hr, hsq, hd, he⟩ :=
    exists_tensorProduct_nine_diagram R A B h₁ h₂
  exact ⟨⟨u, p, d₁, h₁, v, q, d₂, h₂, E, a, c, e₁, e₂, ht, hr, hsq, hd, he⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end TorIndependent

end CommAlgCat

end
