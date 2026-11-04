module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# Ingredients of a naive obstruction theory (Stacks chapter Artin's Axioms)

This file defines two objects of the derived category `D(A)` attached to a commutative ring
`A`, together with morphisms between them.

The first is the *extended alternating Čech complex* of a finite family `f` in `A`, whose
degree-`p` term is the direct sum of the localizations `A_(∏ i ∈ s, f i)` over the `p`-element
subsets `s` of the index set, with its canonical augmentation to `A` placed in degree zero. Given
a derived tensor product on `D(A)`, recorded as a structure `DerivedTensorProduct` (a bifunctor
together with comparisons to the tensor product of complexes exhibiting it as the total left
derived functor in each variable, and with the standard exact, symmetric and unital structure),
the augmentation induces a natural morphism `Č(f) ⊗ᴸ_A - ⟶ id` of endofunctors of `D(A)`.

The second is the *naive cotangent complex* `NL_{A/Λ}`, placed in cohomological degrees
`-1` and `0` and regarded as an object of `D(A)`, together with the natural morphism
`NL_{A/Λ} ⟶ NL_{A/Λ'}` attached to a tower `Λ → Λ' → A` and the base-change map on
Kähler differentials along such a tower.

## Main definitions

* `Deformation.Artin.extendedCechAugmentation`: the canonical augmentation `Č(f) ⟶ A[0]`
  of the extended alternating Čech complex.
* `Deformation.Artin.extendedCechComplexInt`: the extended alternating Čech complex,
  extended by zero from nonnegative to all integral degrees.
* `Deformation.Artin.extendedCechObject`: the corresponding object of `D(A)`, and
  `Deformation.Artin.extendedCechAugmentationHom` its augmentation there.
* `Deformation.Artin.DerivedTensorProduct`: a derived tensor product on `D(A)`,
  characterized by its total-left-derived universal property in each variable.
* `Deformation.Artin.extendedCechTensorToId`: the induced natural morphism
  `Č(f) ⊗ᴸ_A - ⟶ id`.
* `Deformation.Artin.derivedNaiveCotangentComplex`: the naive cotangent complex as an
  object of the derived category.
* `Deformation.Artin.naiveCotangentBaseMap`: the morphism of naive cotangent complexes
  attached to a tower of rings.
* `Deformation.Artin.differentialsBaseChangeMap`: the canonical map
  `k ⊗_{A'} Ω_{A'/Λ} ⟶ k ⊗_A Ω_{A/Λ}` for a tower `Λ → A' → A → k`.

## References

* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Section 47.9](https://stacks.math.columbia.edu/tag/0A6P)
-/

@[expose] public section

namespace Deformation.Artin

section
open CategoryTheory CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe u

/-! ### The extended alternating Čech complex and its augmentation -/

variable (A : Type u) [CommRing A] {r : ℕ}

/-- The degree-zero component of the canonical augmentation from the extended Čech complex
to `A`. The unique degree-zero summand is the localization of `A` at `1`. -/
public noncomputable def extendedCechAugmentationZero (f : Fin r → A) :
    (Cech.cechComplex f A).X 0 ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom <| DirectSum.toModule A _ _ fun s ↦
    LocalizedModule.lift (Cech.cechSub f s.1) LinearMap.id (fun x ↦ by
      obtain ⟨n, hn⟩ := x.2
      simp [show (x : A) = 1 by simpa [Finset.card_eq_zero.mp s.2] using hn.symm])

/-- The canonical augmentation `C(f) ⟶ A[0]` of the extended alternating Čech complex. -/
public noncomputable def extendedCechAugmentation (f : Fin r → A) :
    Cech.cechComplex f A ⟶
      (HomologicalComplex.single (ModuleCat A) (ComplexShape.up ℕ) 0).obj
        (ModuleCat.of A A) :=
  (CochainComplex.toSingle₀Equiv _ _).symm (extendedCechAugmentationZero A f)

/-- The extended alternating Čech complex, extended by zero from nonnegative integral
degrees to all integral degrees. -/
public noncomputable def extendedCechComplexInt (f : Fin r → A) :
    CochainComplex (ModuleCat A) ℤ :=
  (Cech.cechComplex f A).extend ComplexShape.embeddingUpNat

/-- The canonical augmentation of the integral-degree model of the extended Čech complex. -/
public noncomputable def extendedCechAugmentationInt (f : Fin r → A) :
    extendedCechComplexInt A f ⟶
      (CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A) :=
  HomologicalComplex.extendMap (extendedCechAugmentation A f) ComplexShape.embeddingUpNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat
      (ModuleCat.of A A) 0 0 rfl).hom

/-- The derived category `D(A)` of `A`-modules. -/
public abbrev DerivedCategoryOfRing := DerivedCategory (ModuleCat A)

/-- The ring `A`, regarded as the object `A[0]` of `D(A)`. -/
public noncomputable abbrev ringObject : DerivedCategoryOfRing A :=
  (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A)

/-- The object of `D(A)` represented by the extended alternating Čech complex. -/
public noncomputable abbrev extendedCechObject (f : Fin r → A) : DerivedCategoryOfRing A :=
  DerivedCategory.Q.obj (extendedCechComplexInt A f)

/-- The canonical augmentation `C(f) ⟶ A[0]` in the derived category. -/
public noncomputable def extendedCechAugmentationHom (f : Fin r → A) :
    extendedCechObject A f ⟶ ringObject A :=
  DerivedCategory.Q.map (extendedCechAugmentationInt A f)

/-- Tensoring with `L`, followed by passage to the derived category. -/
public noncomputable abbrev complexTensorLeft (L : CochainComplex (ModuleCat A) ℤ) :
    CochainComplex (ModuleCat A) ℤ ⥤ DerivedCategoryOfRing A :=
  ((MonoidalCategory.curriedTensor (ModuleCat A)).map₂CochainComplex).flip.obj L ⋙
    DerivedCategory.Q

/-- Tensoring with `K`, followed by passage to the derived category. -/
public noncomputable abbrev complexTensorRight (K : CochainComplex (ModuleCat A) ℤ) :
    CochainComplex (ModuleCat A) ℤ ⥤ DerivedCategoryOfRing A :=
  ((MonoidalCategory.curriedTensor (ModuleCat A)).map₂CochainComplex).obj K ⋙
    DerivedCategory.Q

/-- A derived tensor product on `D(A)`, characterized by its total-left-derived universal
property in both variables and equipped with its standard exact, symmetric, unital
structure. -/
public structure DerivedTensorProduct where
  /-- The bifunctor `(K, L) ↦ K ⊗ᴸ_A L`. -/
  tensor : DerivedCategoryOfRing A ⥤ DerivedCategoryOfRing A ⥤ DerivedCategoryOfRing A
  /-- Comparison from derived tensoring in the first variable to chain-level tensoring. -/
  comparison_left : ∀ L : CochainComplex (ModuleCat A) ℤ,
    DerivedCategory.Q ⋙ tensor.flip.obj (DerivedCategory.Q.obj L) ⟶ complexTensorLeft A L
  /-- The preceding comparison exhibits the total left derived functor. -/
  isLeftDerived_left : ∀ L : CochainComplex (ModuleCat A) ℤ,
    (tensor.flip.obj (DerivedCategory.Q.obj L)).IsLeftDerivedFunctor
      (comparison_left L) (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ))
  /-- Comparison from derived tensoring in the second variable to chain-level tensoring. -/
  comparison_right : ∀ K : CochainComplex (ModuleCat A) ℤ,
    DerivedCategory.Q ⋙ tensor.obj (DerivedCategory.Q.obj K) ⟶ complexTensorRight A K
  /-- The preceding comparison exhibits the total left derived functor. -/
  isLeftDerived_right : ∀ K : CochainComplex (ModuleCat A) ℤ,
    (tensor.obj (DerivedCategory.Q.obj K)).IsLeftDerivedFunctor
      (comparison_right K) (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ))
  /-- Derived tensor product is additive in its first variable. -/
  add_left : ∀ L, (tensor.flip.obj L).Additive
  /-- Derived tensor product is additive in its second variable. -/
  add_right : ∀ K, (tensor.obj K).Additive
  /-- Tensoring in the first variable commutes with shifts. -/
  commShift_left : ∀ L, (tensor.flip.obj L).CommShift ℤ
  /-- Tensoring in the second variable commutes with shifts. -/
  commShift_right : ∀ K, (tensor.obj K).CommShift ℤ
  /-- Tensoring in the first variable is triangulated. -/
  triangulated_left : ∀ L, letI := commShift_left L; (tensor.flip.obj L).IsTriangulated
  /-- Tensoring in the second variable is triangulated. -/
  triangulated_right : ∀ K, letI := commShift_right K; (tensor.obj K).IsTriangulated
  /-- The symmetry `K ⊗ᴸ_A L ≅ L ⊗ᴸ_A K`. -/
  braiding : tensor ≅ tensor.flip
  /-- The left unit isomorphism `A[0] ⊗ᴸ_A K ≅ K`. -/
  leftUnitor : tensor.obj (ringObject A) ≅ Functor.id (DerivedCategoryOfRing A)
  /-- The derived left unitor agrees, under the comparison map, with the canonical left
  unitor of the tensor product of complexes. -/
  leftUnitor_compatibility : ∀ K : CochainComplex (ModuleCat A) ℤ,
    (comparison_right
        ((CochainComplex.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A))).app K ≫
      DerivedCategory.Q.map (HomologicalComplex.leftUnitor K).hom =
        leftUnitor.hom.app (DerivedCategory.Q.obj K)

/-- The natural morphism `C(f) ⊗ᴸ_A K ⟶ K`, functorial in `K`, induced by the
canonical augmentation `C(f) ⟶ A[0]`. -/
@[implicit_reducible]
public noncomputable def extendedCechTensorToId (T : DerivedTensorProduct A) (f : Fin r → A) :
    T.tensor.obj (extendedCechObject A f) ⟶ Functor.id (DerivedCategoryOfRing A) :=
  T.tensor.map (extendedCechAugmentationHom A f) ≫ T.leftUnitor.hom

end

/-! ### The naive cotangent complex in the derived category -/

section
open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The naive cotangent complex, placed in cohomological degrees `-1` and `0`, as an object
of the derived category. -/
public noncomputable def derivedNaiveCotangentComplex
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    DerivedCategory (ModuleCat.{u} S) :=
  let P := Algebra.Generators.self R S
  DerivedCategory.Q.obj
    (HomologicalComplex.double
      (ModuleCat.ofHom P.toExtension.cotangentComplex)
      (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl))

/-- The natural map `NL_{S/R} ⟶ NL_{S/R'}` associated to a tower `R → R' → S`, in the
derived category of `S`-modules. -/
public noncomputable def naiveCotangentBaseMap
    (R R' S : Type u) [CommRing R] [CommRing R'] [CommRing S]
    [Algebra R R'] [Algebra R S] [Algebra R' S] [IsScalarTower R R' S] :
    derivedNaiveCotangentComplex R S ⟶ derivedNaiveCotangentComplex R' S := by
  let P := Algebra.Generators.self R S
  let P' := Algebra.Generators.self R' S
  let g := P.defaultHom P'
  let f₁ : P.toExtension.Cotangent →ₗ[S] P'.toExtension.Cotangent :=
    (Algebra.Extension.Cotangent.map g.toExtensionHom).restrictScalars S
  let f₀ : P.toExtension.CotangentSpace →ₗ[S] P'.toExtension.CotangentSpace :=
    (Algebra.Extension.CotangentSpace.map g.toExtensionHom).restrictScalars S
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := rfl
  let hne : (-1 : ℤ) ≠ 0 := by omega
  let K := HomologicalComplex.double
    (ModuleCat.ofHom P.toExtension.cotangentComplex) hrel
  let K' := HomologicalComplex.double
    (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel
  let φ : K ⟶ K' := HomologicalComplex.mkHomFromDouble
    hrel hne
    (ModuleCat.ofHom f₁ ≫
      (HomologicalComplex.doubleXIso₀
        (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel).inv)
    (ModuleCat.ofHom f₀ ≫
      (HomologicalComplex.doubleXIso₁
        (ModuleCat.ofHom P'.toExtension.cotangentComplex) hrel hne).inv)
    (by
      rw [HomologicalComplex.double_d _ _ hne]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hmap : ModuleCat.ofHom f₁ ≫
          ModuleCat.ofHom P'.toExtension.cotangentComplex =
          ModuleCat.ofHom P.toExtension.cotangentComplex ≫ ModuleCat.ofHom f₀ :=
        ModuleCat.hom_ext <| LinearMap.ext fun x ↦
          (Algebra.Extension.CotangentSpace.map_cotangentComplex g.toExtensionHom x).symm
      rw [← Category.assoc, hmap, Category.assoc])
    (fun k hk ↦ by
      rw [HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by omega)]
      simp)
  exact DerivedCategory.Q.map φ

/-- The canonical map
`k ⊗_{A'} Ω_{A'/R} ⟶ k ⊗_A Ω_{A/R}` for a tower `R → A' → A → k`. -/
public noncomputable def differentialsBaseChangeMap
    (R A' A k : Type u) [CommRing R] [CommRing A'] [CommRing A] [CommRing k]
    [Algebra R A'] [Algebra R A] [Algebra A' A] [Algebra A k] [Algebra A' k]
    [Algebra R k] [IsScalarTower R A' A] [IsScalarTower R A k]
    [IsScalarTower R A' k] [IsScalarTower A' A k] :
    k ⊗[A'] KaehlerDifferential R A' →ₗ[k] k ⊗[A] KaehlerDifferential R A :=
  (KaehlerDifferential.mapBaseChange R A' A).baseChange k ∘ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A' A k k
      (KaehlerDifferential R A')).symm.toLinearMap

end

end Deformation.Artin
