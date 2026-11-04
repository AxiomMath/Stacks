module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeFiltration.CanonicalCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.TotalCupPairingLaws

/-!
# Associativity and graded commutativity of the cup product along a multiplication

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`. For
`ℕ`-indexed complexes `K`, `L`, `M` of sheaves of `A`-modules and a multiplication
`m : Tot(K ⊗_A L) ⟶ M`, `AlgebraicGeometry.SheafOfModules.canonicalPairingModule m` is the cup
product of Cohomology, Section 0FKU along `m`,

`H^i(X, K) × H^j(X, L) ⟶ H^{i+j}(X, K ⊗^𝐋 L) ⟶ H^{i+j}(X, Tot(K ⊗ L)) ⟶ H^{i+j}(X, M)`.

This file proves the two laws that Cohomology, Lemmas 0FP4 and 0FP5 give it: it is associative
whenever the multiplications are, and graded commutative whenever the multiplications are, the
identities of the multiplications being read in the symmetric monoidal category of complexes of
Tag 0FPQ on the extensions by zero. It is also additive and `ℤ`-linear in the multiplication.

## Main results

* `AlgebraicGeometry.SheafOfModules.canonicalPairingModule_apply`: the cup product along `m` is the
  cup product on total tensor complexes followed by the extended multiplication.
* `AlgebraicGeometry.SheafOfModules.canonicalPairingModule_assoc`: **associativity**,
  `(x ∪ y) ∪ z = x ∪ (y ∪ z)` whenever `m₂ ∘ (m₁ ⊗ 1) = m₄ ∘ (1 ⊗ m₃) ∘ α`.
* `AlgebraicGeometry.SheafOfModules.canonicalPairingModule_comm`: **graded commutativity**,
  `x ∪ y = (-1)^{ij} y ∪' x` whenever `m' ∘ β = m`.
* `AlgebraicGeometry.SheafOfModules.canonicalPairingModule_add` and
  `AlgebraicGeometry.SheafOfModules.canonicalPairingModule_zsmul`: linearity in the
  multiplication.

## Implementation notes

The hypotheses are stated exactly as the conclusions of
`AlgebraicGeometry.SheafOfModules.multiplicationInt_assoc` and
`AlgebraicGeometry.SheafOfModules.multiplicationInt_braiding`, which derive them from identities
of the multiplications on local pure tensors of summands, and under the same local instances. The
two laws on total tensor complexes they are reduced to are
`Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_assoc_of_comp` and
`Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_comm_of_comp`; the extensions by zero are
bounded below, which is what those need.

The degree of a triple product is `(i + j) + k` on one side and `i + (j + k)` on the other, and
that of a product in the other order is `j + i`; the two sides are compared through
`Stacks.Cohomology.DerivedGlobalCupProduct.cohomologyCast`, the identification of cohomology in
equal degrees.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FP5](https://stacks.math.columbia.edu/tag/0FP5)
* [Stacks Project, Tag 0FPQ](https://stacks.math.columbia.edu/tag/0FPQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape Opposite
open TopologicalSpace
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open scoped Stacks.Topology.SheafTensorAdditiveOnOpens TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

variable {K L M : CochainComplex
  (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}

/-- The cup product along `m` is the cup product on total tensor complexes followed by the
extended multiplication. -/
private theorem canonicalPairingModule_eq_comp (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (i j : ℤ) :
    canonicalPairingModule m i j =
      totalCupPairing (S := baseRingedSpace A) (K.extend embeddingUpNat) (L.extend embeddingUpNat)
        i j ≫ cohomologyMap (S := baseRingedSpace A) (multiplicationInt m) (i + j) := by
  unfold canonicalPairingModule totalCupPairing cohomologyMap
  refine (congrArg (cupPairing (cupProductOnSpace (baseRingedSpace A)) (moduleDerived K)
    (moduleDerived L) i j ≫ ·) ((congrArg
      (DerivedCategory.homologyFunctor (ModuleCat (baseRing (baseRingedSpace A))) (i + j)).map
      ((baseSections (baseRingedSpace A)).map_comp _ _)).trans
      ((DerivedCategory.homologyFunctor _ (i + j)).map_comp _ _))).trans ?_
  exact (Category.assoc _ _ _).symm

/-- **The cup product along a multiplication, elementwise**: the cup product of the total tensor
complexes of the extensions by zero, followed by the extended multiplication. -/
theorem canonicalPairingModule_apply (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (i j : ℤ) (x : cohomologyModule (moduleDerived K) i)
    (y : cohomologyModule (moduleDerived L) j) :
    (canonicalPairingModule m i j).hom (x ⊗ₜ y) =
      (cohomologyMap (S := baseRingedSpace A) (multiplicationInt m) (i + j)).hom
        (cupClass (S := baseRingedSpace A) (K.extend embeddingUpNat) (L.extend embeddingUpNat)
          rfl x y) := by
  rw [canonicalPairingModule_eq_comp]
  rfl

/-- The extended multiplication is additive in the multiplication. -/
theorem multiplicationInt_add (m m' : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) :
    multiplicationInt (m + m') = multiplicationInt m + multiplicationInt m' := by
  unfold multiplicationInt
  rw [HomologicalComplex.extendMap_add]
  exact Preadditive.comp_add _ _ _ _ _ _

/-- The extended multiplication is `ℤ`-linear in the multiplication. -/
theorem multiplicationInt_zsmul (c : ℤ) (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) :
    multiplicationInt (c • m) = c • multiplicationInt m := by
  unfold multiplicationInt
  have e : HomologicalComplex.extendMap (c • m) embeddingUpNat =
      c • HomologicalComplex.extendMap m embeddingUpNat :=
    (embeddingUpNat.extendFunctor _).map_zsmul (f := m) (r := c)
  rw [e]
  exact Preadditive.comp_zsmul _ _ c

/-- **The cup product along a multiplication is additive in the multiplication.** -/
theorem canonicalPairingModule_add (m m' : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (i j : ℤ) :
    canonicalPairingModule (m + m') i j =
      canonicalPairingModule m i j + canonicalPairingModule m' i j := by
  rw [canonicalPairingModule_eq_comp, canonicalPairingModule_eq_comp m,
    canonicalPairingModule_eq_comp m']
  refine (congrArg (_ ≫ ·) ((congrArg (cohomologyMap (S := baseRingedSpace A) · (i + j))
    (multiplicationInt_add m m')).trans (cohomologyMap_add _ _ _))).trans ?_
  exact Preadditive.comp_add _ _ _ _ _ _

/-- **The cup product along a multiplication is `ℤ`-linear in the multiplication.** -/
theorem canonicalPairingModule_zsmul (c : ℤ)
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M) (i j : ℤ) :
    canonicalPairingModule (c • m) i j = c • canonicalPairingModule m i j := by
  rw [canonicalPairingModule_eq_comp, canonicalPairingModule_eq_comp m]
  refine (congrArg (_ ≫ ·) ((congrArg (cohomologyMap (S := baseRingedSpace A) · (i + j))
    (multiplicationInt_zsmul c m)).trans (cohomologyMap_zsmul _ _ _))).trans ?_
  exact Preadditive.comp_zsmul _ _ c

/-- The extension by zero of an `ℕ`-indexed complex is bounded below. -/
theorem isStrictlyGE_extend (K : CochainComplex
    (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ) :
    ∃ n : ℤ, CochainComplex.IsStrictlyGE (K.extend embeddingUpNat) n :=
  ⟨0, inferInstance⟩

variable {N P Q : CochainComplex
  (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ}

section Monoidal

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

/-- The associativity identity of four multiplications, read at the spelling of iterated
`HomologicalComplex.mapBifunctor` over the ringed space `(X, A)`. -/
theorem multiplicationInt_assoc_mapBifunctor
    (m₁ : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ P)
    (m₂ : ((tensorBifunctorNat (A := A)).obj P).obj N ⟶ M)
    (m₃ : ((tensorBifunctorNat (A := A)).obj L).obj N ⟶ Q)
    (m₄ : ((tensorBifunctorNat (A := A)).obj K).obj Q ⟶ M)
    (hm : (multiplicationInt m₁ ⊗ₘ 𝟙 (N.extend embeddingUpNat)) ≫ multiplicationInt m₂ =
      (α_ (K.extend embeddingUpNat) (L.extend embeddingUpNat) (N.extend embeddingUpNat)).hom ≫
        (𝟙 (K.extend embeddingUpNat) ⊗ₘ multiplicationInt m₃) ≫ multiplicationInt m₄) :
    HomologicalComplex.mapBifunctorMap (multiplicationInt m₁) (𝟙 (N.extend embeddingUpNat))
        (sheafTensor A) (ComplexShape.up ℤ) ≫ multiplicationInt m₂ =
      tensorAssociator (S := baseRingedSpace A) (K.extend embeddingUpNat)
          (L.extend embeddingUpNat) (N.extend embeddingUpNat) ≫
        HomologicalComplex.mapBifunctorMap (𝟙 (K.extend embeddingUpNat)) (multiplicationInt m₃)
          (sheafTensor A) (ComplexShape.up ℤ) ≫ multiplicationInt m₄ :=
  hm

/-- **The cup product along multiplications of complexes is associative** as soon as the
multiplications are. Let `m₁ : Tot(K ⊗ L) ⟶ P`, `m₂ : Tot(P ⊗ N) ⟶ M`, `m₃ : Tot(L ⊗ N) ⟶ Q` and
`m₄ : Tot(K ⊗ Q) ⟶ M` be multiplications of `ℕ`-indexed complexes of sheaves of `A`-modules whose
extensions by zero satisfy `m₂ ∘ (m₁ ⊗ 1) = m₄ ∘ (1 ⊗ m₃) ∘ α` for the associator `α` of the
symmetric monoidal category of complexes (Tag 0FPQ). Then for classes `x`, `y`, `z` in degrees
`i`, `j`, `k`, `(x ∪ y) ∪ z = x ∪ (y ∪ z)`, the left-hand side read in degree `i + (j + k)`.

This is Cohomology, Lemma 0FP4 in the form the source uses it for the de Rham complex: the proof
is `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_assoc`, the associativity of the cup
product on total tensor complexes, together with the identity of the multiplications. -/
theorem canonicalPairingModule_assoc
    (m₁ : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ P)
    (m₂ : ((tensorBifunctorNat (A := A)).obj P).obj N ⟶ M)
    (m₃ : ((tensorBifunctorNat (A := A)).obj L).obj N ⟶ Q)
    (m₄ : ((tensorBifunctorNat (A := A)).obj K).obj Q ⟶ M)
    (hm : (multiplicationInt m₁ ⊗ₘ 𝟙 (N.extend embeddingUpNat)) ≫ multiplicationInt m₂ =
      (α_ (K.extend embeddingUpNat) (L.extend embeddingUpNat) (N.extend embeddingUpNat)).hom ≫
        (𝟙 (K.extend embeddingUpNat) ⊗ₘ multiplicationInt m₃) ≫ multiplicationInt m₄)
    (i j k : ℤ) (x : cohomologyModule (moduleDerived K) i)
    (y : cohomologyModule (moduleDerived L) j) (z : cohomologyModule (moduleDerived N) k) :
    (cohomologyCast (moduleDerived M) (add_assoc i j k)).hom
        ((canonicalPairingModule m₂ (i + j) k).hom
          ((canonicalPairingModule m₁ i j).hom (x ⊗ₜ y) ⊗ₜ z)) =
      (canonicalPairingModule m₄ i (j + k)).hom
        (x ⊗ₜ (canonicalPairingModule m₃ j k).hom (y ⊗ₜ z)) := by
  have hm' := multiplicationInt_assoc_mapBifunctor m₁ m₂ m₃ m₄ hm
  have e := cupClass_assoc_of_comp (S := baseRingedSpace A) (isStrictlyGE_extend K)
    (isStrictlyGE_extend L) (isStrictlyGE_extend N) (multiplicationInt m₁) (multiplicationInt m₂)
    (multiplicationInt m₃) (multiplicationInt m₄) hm' i j k x y z
  refine Eq.trans ?_ (e.trans ?_)
  · refine congrArg (cohomologyCast (moduleDerived M) (add_assoc i j k)).hom ?_
    refine (congrArg (fun t => (canonicalPairingModule m₂ (i + j) k).hom (t ⊗ₜ z))
      (canonicalPairingModule_apply m₁ i j x y)).trans ?_
    exact canonicalPairingModule_apply m₂ (i + j) k _ z
  · refine Eq.trans ?_ (canonicalPairingModule_apply m₄ i (j + k) x _).symm
    exact congrArg (fun t => (cohomologyMap (S := baseRingedSpace A) (multiplicationInt m₄)
      (i + (j + k))).hom (cupClass (S := baseRingedSpace A) (K.extend embeddingUpNat)
        (Q.extend embeddingUpNat) rfl x t)) (canonicalPairingModule_apply m₃ j k y z).symm

end Monoidal

section Symmetric

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexSymmetricCategory

/-- The commutativity identity of two multiplications, read at the spelling of
`HomologicalComplex.mapBifunctor` over the ringed space `(X, A)`. -/
theorem multiplicationInt_braiding_mapBifunctor
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj L).obj K ⟶ M)
    (hm : (β_ (K.extend embeddingUpNat) (L.extend embeddingUpNat)).hom ≫ multiplicationInt m' =
      multiplicationInt m) :
    tensorBraiding (S := baseRingedSpace A) (K.extend embeddingUpNat) (L.extend embeddingUpNat) ≫
      multiplicationInt m' = multiplicationInt m :=
  hm

/-- **The cup product along multiplications of complexes is graded commutative** as soon as the
multiplications are. Let `m : Tot(K ⊗ L) ⟶ M` and `m' : Tot(L ⊗ K) ⟶ M` be multiplications of
`ℕ`-indexed complexes of sheaves of `A`-modules whose extensions by zero satisfy `m' ∘ β = m` for
the Koszul symmetry `β` of the symmetric monoidal category of complexes (Tag 0FPQ). Then for
classes `x`, `y` in degrees `i`, `j`, `x ∪ y = (-1)^{ij} y ∪' x`, the right-hand side read in
degree `i + j`.

This is Cohomology, Lemma 0FP5 in the form the source uses it for the de Rham complex: the proof
is `Stacks.Cohomology.DerivedGlobalCupProduct.cupClass_comm`, the graded commutativity of the cup
product on total tensor complexes, together with the identity of the multiplications. -/
theorem canonicalPairingModule_comm
    (m : ((tensorBifunctorNat (A := A)).obj K).obj L ⟶ M)
    (m' : ((tensorBifunctorNat (A := A)).obj L).obj K ⟶ M)
    (hm : (β_ (K.extend embeddingUpNat) (L.extend embeddingUpNat)).hom ≫ multiplicationInt m' =
      multiplicationInt m) (i j : ℤ)
    (x : cohomologyModule (moduleDerived K) i) (y : cohomologyModule (moduleDerived L) j) :
    (canonicalPairingModule m i j).hom (x ⊗ₜ y) =
      ((i * j).negOnePow : ℤ) • (cohomologyCast (moduleDerived M) (add_comm j i)).hom
        ((canonicalPairingModule m' j i).hom (y ⊗ₜ x)) := by
  have hm' := multiplicationInt_braiding_mapBifunctor m m' hm
  refine (canonicalPairingModule_apply m i j x y).trans ?_
  refine (cupClass_comm_of_comp (S := baseRingedSpace A) (isStrictlyGE_extend K)
    (isStrictlyGE_extend L) (multiplicationInt m) (multiplicationInt m') hm' i j x y).trans ?_
  exact congrArg (fun t => ((i * j).negOnePow : ℤ) •
    (cohomologyCast (moduleDerived M) (add_comm j i)).hom t)
    (canonicalPairingModule_apply m' j i y x).symm

end Symmetric

end AlgebraicGeometry.SheafOfModules
