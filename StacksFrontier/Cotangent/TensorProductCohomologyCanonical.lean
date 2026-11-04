module

public import StacksFrontier.Cotangent.LichtenbaumSchlessingerTensorBaseChangeTor
public import StacksFrontier.Cotangent.TensorProductCohomologyComparison

/-!
# The cohomology of the object `E` of the tensor-product nine diagram

Let `R` be a ring and let `A`, `B` be `R`-algebras. The object `E` of Equation 92.15.0.1 sits in
the distinguished triangle

`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A} ⟶ E ⟶`

of the right column of the nine diagram (Tag 09D9). This file proves [Stacks, Tag 09DB]:

`H^i(E) = 0` for `i ≥ -1`, and `H^{-2}(E) = Tor_1^R(A, B)`,

the latter as an isomorphism of `A ⊗_R B`-modules, `Tor_1^R(A, B)` carrying its canonical
`A ⊗_R B`-module structure (`CommAlgCat.torOneTensorProductModule`).

The proof is the source's. Choose a polynomial presentation `P → B` over `R`, with generators of
the kernel; its base change is a presentation of `A ⊗_R B` over `A`. By Lemma 09CG the canonical
truncations `τ_{≥ -2}` of `L_{B/R}` and `L_{A ⊗_R B/A}` are the Lichtenbaum–Schlessinger complexes
of the two presentations, compatibly with the maps by Remark 09D7; this reduces the computation
to the map of Lichtenbaum–Schlessinger complexes (`CommAlgCat.homologyNegTwoIsoCokernel`,
`CommAlgCat.isZero_homology_of_tensorBaseChangeComplexMap`). In degrees `-1` and `0` that map is an
isomorphism after base change (`Algebra.Presentation.isIso_tensorBaseChangeComplexMap_f_negOne`,
`Algebra.Presentation.isIso_tensorBaseChangeComplexMap_f_zero`), and in degree `-2` its cokernel is
`Tor_1^R(A, B)` (`Algebra.Presentation.cokernelNegTwoIsoTorOne`).

## Main results

* `CommAlgCat.isZero_homology_of_tensorProduct_rightColumn` and
  `CommAlgCat.homologyNegTwoIsoTorOneOfRightColumn`: the two clauses, for every `E` in a
  distinguished triangle on the canonical map of the right column.
* `CommAlgCat.tensorProduct_rightColumn_homology`: **Stacks 09DB** for every such `E`.
* `CommAlgCat.canonicalTensorProductNineDiagram_upperRight_homology`: **Stacks 09DB** for the
  object `E` of the nine diagram `CommAlgCat.canonicalTensorProductNineDiagram` of Tag 09D9, with
  `CommAlgCat.isZero_homology_canonicalTensorProductNineDiagram_upperRight` and
  `CommAlgCat.homologyNegTwoCanonicalUpperRightIsoTorOne` its two clauses.

## References

* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
* [Stacks Project, Tag 09D9](https://stacks.math.columbia.edu/tag/09D9)
* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct

universe u

namespace CommAlgCat

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] HasDerivedCategory.standard

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The presentation of `B` over `R` by the polynomial ring on the elements of `B`, with the
whole kernel as generators. -/
def selfPresentation (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] :
    Algebra.Presentation R B B (Algebra.Generators.self R B).ker :=
  { Algebra.Generators.self R B with
    relation := fun t => t.1
    span_range_relation_eq_ker := by
      rw [Subtype.range_coe_subtype]
      exact Ideal.span_eq (Algebra.Generators.self R B).ker }

/-- On `Tor_1^R(A, B)`, the action of `algebraMap R (A ⊗[R] B) r` through the canonical
`A ⊗_R B`-module structure is the action of `r` through the `R`-module structure. -/
theorem torOneTensorProductModule_algebraMap_smul (r : R) (x : torOneTensorProductModule R A B) :
    (algebraMap R (A ⊗[R] B) r • x : torOneTensorProductModule R A B) =
      r • (show TorChangeOfRings.torObj R 1 A B from x) := by
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R A B 1
  have := TorChangeOfRings.moduleStructure_isScalarTower TorChangeOfRings.canonicalSystem_nonempty
    R A B 1
  exact algebraMap_smul (A ⊗[R] B) r (show TorChangeOfRings.torObj R 1 A B from x)

/-- The identity of `Tor_1^R(A, B)`, from the restriction of scalars of its
`A ⊗_R B`-module structure to its `R`-module structure. -/
def torOneRestrictLinearEquiv :
    ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj
      (torOneTensorProductModule R A B)) ≃ₗ[R] TorChangeOfRings.torObj R 1 A B where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := (ModuleCat.restrictScalars.smul_def _ r x).trans
    (torOneTensorProductModule_algebraMap_smul R A B r x)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The underlying `R`-module of `Tor_1^R(A, B)`, with its `A ⊗_R B`-module structure, is the
categorical `Tor_1^R(A, B)`. -/
def restrictScalarsTorOneTensorProductModuleIso :
    (ModuleCat.restrictScalars (algebraMap R (A ⊗[R] B))).obj (torOneTensorProductModule R A B) ≅
      ((Tor (ModuleCat.{u} R) 1).obj (ModuleCat.of R A)).obj (ModuleCat.of R B) where
  hom := ConcreteCategory.ofHom (C := ModuleCat R) (torOneRestrictLinearEquiv R A B).toLinearMap
  inv :=
    ConcreteCategory.ofHom (C := ModuleCat R) (torOneRestrictLinearEquiv R A B).symm.toLinearMap
  hom_inv_id := rfl
  inv_hom_id := rfl

section RightColumn

variable {R A B} {E : DerivedCategory (ModuleCat.{u} (A ⊗[R] B))}
  {b : cotangentComplexDerived A (CommAlgCat.of A (A ⊗[R] B)) ⟶ E}
  {e : E ⟶ (cotangentComplexDerivedBaseChange R (CommAlgCat.of R B) (A ⊗[R] B))⟦(1 : ℤ)⟧}

/-- **The vanishing clause of Stacks 09DB.** Every object `E` in a distinguished triangle
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A} ⟶ E ⟶` on the canonical map of the right column of
Equation 92.15.0.1 has `H^i(E) = 0` for `i ≥ -1`. -/
theorem isZero_homology_of_tensorProduct_rightColumn
    (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _)
    (i : ℤ) (hi : -1 ≤ i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj E) :=
  isZero_homology_of_tensorBaseChangeComplexMap (P := selfPresentation R B)
    ((selfPresentation R B).epi_tensorBaseChangeComplexMap_f A)
    ((selfPresentation R B).mono_tensorBaseChangeComplexMap_f A)
    ((selfPresentation R B).projective_lichtenbaumSchlessingerComplex_X) hE i hi

/-- **The degree `-2` clause of Stacks 09DB.** Every object `E` in a distinguished triangle on the
canonical map of the right column of Equation 92.15.0.1 has `H^{-2}(E) ≅ Tor_1^R(A, B)` as
`A ⊗_R B`-modules. -/
def homologyNegTwoIsoTorOneOfRightColumn
    (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj E ≅
      torOneTensorProductModule R A B :=
  homologyNegTwoIsoCokernel (P := selfPresentation R B)
      ((selfPresentation R B).epi_tensorBaseChangeComplexMap_f A)
      ((selfPresentation R B).mono_tensorBaseChangeComplexMap_f A)
      ((selfPresentation R B).projective_lichtenbaumSchlessingerComplex_X) hE ≪≫
    (selfPresentation R B).cokernelNegTwoIsoTorOne A

/-- **Stacks 09DB**, for every cone `E` of the canonical map
`L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}` of the right column of Equation 92.15.0.1:
`H^i(E) = 0` for `i ≥ -1` and `H^{-2}(E) ≅ Tor_1^R(A, B)` as `A ⊗_R B`-modules. -/
@[stacks 09DB "for every object E in a distinguished triangle on the canonical map \
L_{B/R} ⊗^L_B (A ⊗_R B) → L_{A ⊗_R B/A} of the right column of Equation 92.15.0.1, which is how \
the source's proof describes E: H^i(E) = 0 for i ≥ -1 and H^{-2}(E) ≅ Tor_1^R(A, B) as \
A ⊗_R B-modules, Tor_1 with its canonical module structure"]
theorem tensorProduct_rightColumn_homology
    (hE : Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B) b e ∈ distTriang _) :
    (∀ i : ℤ, -1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj E)) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj E ≅
        torOneTensorProductModule R A B) :=
  ⟨isZero_homology_of_tensorProduct_rightColumn hE, ⟨homologyNegTwoIsoTorOneOfRightColumn hE⟩⟩

end RightColumn

/-- The right column of the nine diagram of Tag 09D9 is a distinguished triangle on the
canonical map `L_{B/R} ⊗^L_B (A ⊗_R B) ⟶ L_{A ⊗_R B/A}`. -/
theorem canonicalTensorProductNineDiagram_rightColumn :
    Triangle.mk (cotangentTensorProductBaseChangeMapRight R A B)
        (canonicalTensorProductNineDiagram R A B).fromA
        (canonicalTensorProductNineDiagram R A B).toShiftB ∈ distTriang _ := by
  have h := (canonicalTensorProductNineDiagram R A B).rightColumnDistinguished
  obtain ⟨-, hp, -, hv, -, -⟩ := canonicalTensorProductNineDiagram_spec R A B
  rw [hp, hv, fundamentalMor₁_comp_fundamentalMor₂_includeRight] at h
  exact h

/-- **The vanishing clause of Stacks 09DB** for the object `E` of the nine diagram of
Tag 09D9. -/
theorem isZero_homology_canonicalTensorProductNineDiagram_upperRight (i : ℤ) (hi : -1 ≤ i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj
      (canonicalTensorProductNineDiagram R A B).upperRight) :=
  isZero_homology_of_tensorProduct_rightColumn
    (canonicalTensorProductNineDiagram_rightColumn R A B) i hi

/-- **The degree `-2` clause of Stacks 09DB** for the object `E` of the nine diagram of
Tag 09D9: `H^{-2}(E) ≅ Tor_1^R(A, B)` as `A ⊗_R B`-modules. -/
def homologyNegTwoCanonicalUpperRightIsoTorOne :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
        (canonicalTensorProductNineDiagram R A B).upperRight ≅
      torOneTensorProductModule R A B :=
  homologyNegTwoIsoTorOneOfRightColumn (canonicalTensorProductNineDiagram_rightColumn R A B)

/-- **Stacks 09DB.** Let `R` be a ring and let `A`, `B` be `R`-algebras. The object `E` of
Equation 92.15.0.1 satisfies `H^i(E) = 0` for `i ≥ -1` and `H^{-2}(E) = Tor_1^R(A, B)`, the
latter as an isomorphism of `A ⊗_R B`-modules. -/
@[stacks 09DB "the object E of the nine diagram of Tag 09D9, \
CommAlgCat.canonicalTensorProductNineDiagram: H^i(E) = 0 for i ≥ -1 and H^{-2}(E) ≅ \
Tor_1^R(A, B) as A ⊗_R B-modules, Tor_1 with its canonical module structure \
(CommAlgCat.torOneTensorProductModule); the isomorphism itself is \
CommAlgCat.homologyNegTwoCanonicalUpperRightIsoTorOne"]
theorem canonicalTensorProductNineDiagram_upperRight_homology :
    (∀ i : ℤ, -1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) i).obj
        (canonicalTensorProductNineDiagram R A B).upperRight)) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⊗[R] B)) (-2)).obj
          (canonicalTensorProductNineDiagram R A B).upperRight ≅
        torOneTensorProductModule R A B) :=
  ⟨isZero_homology_canonicalTensorProductNineDiagram_upperRight R A B,
    ⟨homologyNegTwoCanonicalUpperRightIsoTorOne R A B⟩⟩

end CommAlgCat
