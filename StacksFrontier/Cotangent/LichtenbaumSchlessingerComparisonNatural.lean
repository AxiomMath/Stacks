module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonRelative
public import StacksFrontier.Cotangent.StandardResolutionSquareFunctoriality

/-!
# Naturality of the comparison `L_{B/A} → L` along a square of rings

This file proves the second commutative diagram of [Stacks, Tag 09D7]: for a commutative square
of rings `A → A'`, `B → B'` and compatible presentations `P → P'` with `f'_t` the image of
`f_t`, the canonical maps `L_{B/A} → L` and `L_{B'/A'} → L'` of [Stacks, Tag 09CG] commute in
`D(B)` with the map `L_{B/A} → L_{B'/A'}` of cotangent complexes and the map `L → L'` of
Lichtenbaum–Schlessinger complexes.

## Main definitions

* `Algebra.Presentation.cotangentComplexULiftSquareMap`: the map `L_{B/A} → L_{B'/A'}`.

## Main results

* `LichtenbaumSchlessingerHom.canonicalCotangentToLichtenbaumSchlessinger_naturality`: the second
  diagram of Tag 09D7 commutes.

## Implementation notes

Both composites are maps of complexes `L_{B/A} → L'` given by the formulas of Tag 09CG for a
relative choice: `(ψ ∘ (P → P'), λ ↦ image of λ)` and `((P'₀ → P') ∘ (P₀ → P'₀), λ' ∘ (P₁ → P'₁))`.
By `Algebra.Presentation.homotopyOfIsLichtenbaumSchlessingerRelativeComparison` they are
homotopic.

## References

* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial TensorProduct KaehlerDifferential
open Stacks.Cotangent

universe u u' v w

noncomputable section

namespace Algebra.Presentation

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} {A' : Type u'} {B B' : Type (max u u' v)}
  [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
  [IsScalarTower A A' B'] [IsScalarTower A B B']

variable (A A' B B') in
/-- The commutative square of rings `A → A'`, `B → B'`. -/
def algebraSquare : CommAlgCat.AlgebraSquare.{u, v, u'} A A' (CommAlgCat.of A B)
    (CommAlgCat.of A' B') where
  base := algebraMap A A'
  map := algebraMap B B'
  map_algebraMap a := by
    change algebraMap B B' (algebraMap A B a) = algebraMap A' B' (algebraMap A A' a)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

variable (A A' B B') in
/-- **The map of cotangent complexes `L_{B/A} → L_{B'/A'}`** of the square, lifted to the module
universe of the Lichtenbaum–Schlessinger complexes. -/
def cotangentComplexULiftSquareMap : cotangentComplexULift.{u, max u' v, w} A B ⟶
    ((ModuleCat.restrictScalars (algebraMap B B')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (cotangentComplexULift.{u', max u v, w} A' B') :=
  ((ModuleCat.uliftFunctor.{w} B).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (CommAlgCat.squareCotangentComplexMap.{u, v, u'} (algebraSquare A A' B B'))

variable (A B) in
/-- The two universe lifts of the cotangent complex used here. -/
def cotangentComplexULiftIso : cotangentComplexULift.{u, max u' v, w} A B ≅
    cotangentComplexULift.{u, max u' v, max u' w} A B :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ => (ULift.moduleEquiv.trans ULift.moduleEquiv.symm).toModuleIso)
    (fun _ _ _ => ModuleCat.hom_ext (LinearMap.ext fun _ => rfl))

/-! ### The choice through `L_{B'/A'}` -/

local notation "𝓊" n => CommAlgCat.standardResolutionSquareMap
  (algebraSquare A A' B B') (op ⦋n⦌)

variable {X' T' : Type w}

variable (A B) in
/-- `P₀ → P'₀ → P'`. -/
def innerSection (P' : Presentation A' B' X' T') :
    (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj (op ⦋0⦌) →ₐ[A]
      P'.Ring where
  toRingHom := (lsSection.{u', max u v, w} P').toRingHom.comp (𝓊 0)
  commutes' a := by
    change lsSection.{u', max u v, w} P' ((𝓊 0) (algebraMap A _ a)) = _
    rw [CommAlgCat.standardResolutionSquareMap_algebraMap, AlgHom.commutes]
    exact (IsScalarTower.algebraMap_apply A A' P'.Ring a).symm

/-- `innerSection A B P'` sends `p` to the image of `(P₀ → P'₀) p` under `P'₀ → P'`. -/
theorem innerSection_apply (P' : Presentation A' B' X' T') (p) :
    innerSection A B P' p = lsSection.{u', max u v, w} P' ((𝓊 0) p) := rfl

/-- The composite of `P₁ → P'₁` with `lsBiderivation P'` is `A`-linear. -/
theorem lsBiderivation_squareMap_smul (P' : Presentation A' B' X' T') (a : A)
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋1⦌)) :
    lsBiderivation.{u', max u v, w} P' ((𝓊 1) (a • x)) =
      a • lsBiderivation.{u', max u v, w} P' ((𝓊 1) x) := by
  rw [Algebra.smul_def, map_mul, CommAlgCat.standardResolutionSquareMap_algebraMap,
    ← Algebra.smul_def, lsBiderivation_smul]
  exact algebraMap_smul A' a _

variable (A B) in
/-- **The relative choice `((P'₀ → P') ∘ (P₀ → P'₀), λ' ∘ (P₁ → P'₁))`**: the composite
`L_{B/A} → L_{B'/A'} → L'`. -/
def innerChoice (P' : Presentation A' B' X' T') :
    LichtenbaumSchlessingerRelativeChoice.{u, u', max u' v, w} A B P' where
  ψ := innerSection A B P'
  algebraMap_ψ p := by
    rw [innerSection_apply, algebraMap_lsSection]
    exact CommAlgCat.standardResolutionSquareMap_augmentation_app (algebraSquare A A' B B') _ p
  lam :=
    { toFun := fun x => lsBiderivation.{u', max u v, w} P' ((𝓊 1) x)
      map_add' := fun x y => by rw [map_add, lsBiderivation_add]
      map_smul' := fun a x => lsBiderivation_squareMap_smul P' a x }
  lam_mul x y := by
    change lsBiderivation.{u', max u v, w} P' ((𝓊 1) (x * y)) = _
    rw [map_mul, lsBiderivation_mul, ← CommAlgCat.standardResolutionSquareMap_δ,
      ← CommAlgCat.standardResolutionSquareMap_δ]
    rfl
  freeQuotientRelationMap_lam x := by
    change freeQuotientRelationMap P' (lsBiderivation.{u', max u v, w} P' ((𝓊 1) x)) = _
    rw [freeQuotientRelationMap_lsBiderivation, ← CommAlgCat.standardResolutionSquareMap_δ,
      ← CommAlgCat.standardResolutionSquareMap_δ]
    rfl

/-! ### The two composites are given by the formulas of the source -/

/-- The map `L_{B/A} → L_{B'/A'}` sends the generator `d x` of degree `-n` to `d ((𝓊 n) x)`. -/
private theorem squareCotangentComplexMap_f_degreeIso_inv (n : ℕ)
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋n⦌)) :
    (CommAlgCat.squareCotangentComplexMap.{u, v, u'} (algebraSquare A A' B B')).f (-(n : ℤ))
        ((CommAlgCat.cotangentComplex_degreeIso A (CommAlgCat.of A B) n).inv
          (CommAlgCat.cotangentTermDifferential A (CommAlgCat.of A B) (op ⦋n⦌) x)) =
      (CommAlgCat.cotangentComplex_degreeIso A' (CommAlgCat.of A' B') n).inv
        (CommAlgCat.cotangentTermDifferential A' (CommAlgCat.of A' B') (op ⦋n⦌) ((𝓊 n) x)) :=
  (Iso.hom_inv_id_apply (CommAlgCat.cotangentComplex_degreeIso A' (CommAlgCat.of A' B') n)
    _).symm.trans
    (congrArg _ (CommAlgCat.squareCotangentComplexMap_differential (algebraSquare A A' B B') n x))

/-- In degree `0`, the map `L_{B/A} → L_{B'/A'}` sends `generatorZero x` to
`generatorZero ((P₀ → P'₀) x)`. -/
theorem cotangentComplexULiftSquareMap_generatorZero
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋0⦌)) :
    (cotangentComplexULiftSquareMap.{u, u', v, w} A A' B B').f 0 (generatorZero x) =
      generatorZero.{u', max u v, w} ((𝓊 0) x) := by
  exact congrArg ULift.up (squareCotangentComplexMap_f_degreeIso_inv (A' := A') (B' := B') 0 x)

/-- In degree `-1`, the map `L_{B/A} → L_{B'/A'}` sends `generatorOne x` to
`generatorOne ((P₁ → P'₁) x)`. -/
theorem cotangentComplexULiftSquareMap_generatorOne
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋1⦌)) :
    (cotangentComplexULiftSquareMap.{u, u', v, w} A A' B B').f (-1) (generatorOne x) =
      generatorOne.{u', max u v, w} ((𝓊 1) x) := by
  exact congrArg ULift.up (squareCotangentComplexMap_f_degreeIso_inv (A' := A') (B' := B') 1 x)

/-- In degree `-2`, the map `L_{B/A} → L_{B'/A'}` sends `generatorTwo x` to
`generatorTwo ((P₂ → P'₂) x)`. -/
theorem cotangentComplexULiftSquareMap_generatorTwo
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋2⦌)) :
    (cotangentComplexULiftSquareMap.{u, u', v, w} A A' B B').f (-2) (generatorTwo x) =
      generatorTwo.{u', max u v, w} ((𝓊 2) x) := by
  exact congrArg ULift.up (squareCotangentComplexMap_f_degreeIso_inv (A' := A') (B' := B') 2 x)

/-- The maps `P₂ → P'₂` and `P₁ → P'₁` intertwine `CommAlgCat.faceSumTwo`. -/
theorem faceSumTwo_squareMap
    (g : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋2⦌)) :
    CommAlgCat.faceSumTwo A' (CommAlgCat.of A' B') ((𝓊 2) g) =
      (𝓊 1) (CommAlgCat.faceSumTwo A (CommAlgCat.of A B) g) := by
  rw [CommAlgCat.faceSumTwo_apply, CommAlgCat.faceSumTwo_apply, map_add, map_sub,
    CommAlgCat.standardResolutionSquareMap_δ, CommAlgCat.standardResolutionSquareMap_δ,
    CommAlgCat.standardResolutionSquareMap_δ]

variable (A B) in
/-- The composite `L_{B/A} → L_{B'/A'} → L'`. -/
def innerComposite (P' : Presentation A' B' X' T') :
    cotangentComplexULift.{u, max u' v, w} A B ⟶
      ((ModuleCat.restrictScalars (algebraMap B B')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (lichtenbaumSchlessingerComplex P').complex :=
  cotangentComplexULiftSquareMap.{u, u', v, w} A A' B B' ≫
    ((ModuleCat.restrictScalars (algebraMap B B')).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (lsChainMap.{u', max u v, w} P')

omit [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] in
/-- The inverse of `cotangentComplexULiftIso A B` sends `generatorZero x` to `generatorZero x`. -/
theorem cotangentComplexULiftIso_inv_generatorZero
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋0⦌)) :
    (cotangentComplexULiftIso.{u, u', v, w} A B).inv.f 0 (generatorZero x) =
      generatorZero.{u, max u' v, w} x := rfl

omit [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] in
/-- The inverse of `cotangentComplexULiftIso A B` sends `generatorOne x` to `generatorOne x`. -/
theorem cotangentComplexULiftIso_inv_generatorOne
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋1⦌)) :
    (cotangentComplexULiftIso.{u, u', v, w} A B).inv.f (-1) (generatorOne x) =
      generatorOne.{u, max u' v, w} x := rfl

omit [Algebra A' B'] [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B']
  [IsScalarTower A B B'] in
/-- The inverse of `cotangentComplexULiftIso A B` sends `generatorTwo x` to `generatorTwo x`. -/
theorem cotangentComplexULiftIso_inv_generatorTwo
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋2⦌)) :
    (cotangentComplexULiftIso.{u, u', v, w} A B).inv.f (-2) (generatorTwo x) =
      generatorTwo.{u, max u' v, w} x := rfl

/-- In degree `0`, `innerComposite A B P'` sends `generatorZero x` to `1 ⊗ dψ(x)`, where `ψ` is
the section of `innerChoice A B P'`. -/
theorem innerComposite_zero (P' : Presentation A' B' X' T')
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋0⦌)) :
    (lichtenbaumSchlessingerComplex P').differentialIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ innerComposite A B P').f 0
        (generatorZero x)) = (1 : B') ⊗ₜ D A' P'.Ring (innerChoice A B P' |>.ψ x) := by
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorZero, innerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, cotangentComplexULiftSquareMap_generatorZero]
  exact (isLichtenbaumSchlessingerComparison_lsChainMap.{u', max u v, w} P').zero ((𝓊 0) x)

/-- In degree `-1`, `innerComposite A B P'` sends `generatorOne x` to the image of `λ x`, where
`λ` is the linear map of `innerChoice A B P'`. -/
theorem innerComposite_negOne (P' : Presentation A' B' X' T')
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋1⦌)) :
    (lichtenbaumSchlessingerComplex P').freeIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ innerComposite A B P').f (-1)
        (generatorOne x)) = freeQuotientToTensor P' (innerChoice A B P' |>.lam x) := by
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorOne, innerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, cotangentComplexULiftSquareMap_generatorOne]
  exact (isLichtenbaumSchlessingerComparison_lsChainMap.{u', max u v, w} P').negOne ((𝓊 1) x)

/-- In degree `-2`, `innerComposite A B P'` sends `generatorTwo g` to `1 ⊗ r(g)`, where `r` is
the relation map of `innerChoice A B P'`. -/
theorem innerComposite_negTwo (P' : Presentation A' B' X' T')
    (g : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋2⦌)) :
    (lichtenbaumSchlessingerComplex P').relationIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ innerComposite A B P').f (-2)
        (generatorTwo g)) = (1 : B') ⊗ₜ (innerChoice A B P' |>.relation g) := by
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorTwo, innerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, cotangentComplexULiftSquareMap_generatorTwo]
  refine ((isLichtenbaumSchlessingerComparison_lsChainMap.{u', max u v, w} P').negTwo
    ((𝓊 2) g)).trans (congrArg _ ?_)
  apply relationQuotientToFree_injective P'
  rw [LichtenbaumSchlessingerChoice.relationQuotientToFree_relation,
    LichtenbaumSchlessingerRelativeChoice.relationQuotientToFree_relation]
  change lsBiderivation.{u', max u v, w} P' _ = lsBiderivation.{u', max u v, w} P' _
  rw [faceSumTwo_squareMap]

/-- `innerComposite A B P'` is given by the formulas of the relative choice
`innerChoice A B P'`. -/
theorem isLichtenbaumSchlessingerRelativeComparison_inner (P' : Presentation A' B' X' T') :
    IsLichtenbaumSchlessingerRelativeComparison.{u, u', max u' v, w} P' (innerChoice A B P')
      ((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ innerComposite A B P') where
  zero := innerComposite_zero P'
  negOne := innerComposite_negOne P'
  negTwo := innerComposite_negTwo P'

namespace LichtenbaumSchlessingerHom

variable {X X' T S : Type w} {P : Presentation A B X T} {P' : Presentation A' B' X' (T ⊕ S)}
  (f : LichtenbaumSchlessingerHom P P')

/-- `F/TrivRel → F'/TrivRel'` as an `A`-linear map. -/
def freeQuotientMapₗ : freeQuotient P →ₗ[A] freeQuotient P' where
  toFun := f.freeQuotientMap
  map_add' := map_add _
  map_smul' a m := by
    rw [RingHom.id_apply, ← algebraMap_smul P.Ring a m, map_smulₛₗ, ← algebraMap_smul P'.Ring a]
    congr 1
    exact f.toHom.toAlgHom.commutes a

/-- **The relative choice `(P → P') ∘ ψ`, with `λ` pushed forward**: the composite
`L_{B/A} → L → L'`. -/
def outerChoice : LichtenbaumSchlessingerRelativeChoice.{u, u', max u' v, w} A B P' where
  ψ := f.toHom.toAlgHom.comp (lsSection.{u, max u' v, w} P)
  algebraMap_ψ p := by
    rw [AlgHom.comp_apply]
    exact (f.algebraMap_ringHom _).trans (congrArg _ (algebraMap_lsSection.{u, max u' v, w} P p))
  lam := f.freeQuotientMapₗ ∘ₗ
    { toFun := lsBiderivation.{u, max u' v, w} P
      map_add' := lsBiderivation_add.{u, max u' v, w} P
      map_smul' := lsBiderivation_smul.{u, max u' v, w} P }
  lam_mul x y := by
    change f.freeQuotientMap (lsBiderivation.{u, max u' v, w} P (x * y)) = _
    rw [lsBiderivation_mul, map_add, map_smulₛₗ, map_smulₛₗ]
    rfl
  freeQuotientRelationMap_lam x := by
    change freeQuotientRelationMap P' (f.freeQuotientMap (lsBiderivation.{u, max u' v, w} P x)) = _
    rw [freeQuotientRelationMap_freeQuotientMap, freeQuotientRelationMap_lsBiderivation, map_sub]
    rfl

/-- The composite `L_{B/A} → L → L'`. -/
def outerComposite : cotangentComplexULift.{u, max u' v, w} A B ⟶
    ((ModuleCat.restrictScalars (algebraMap B B')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (lichtenbaumSchlessingerComplex P').complex :=
  lsChainMap.{u, max u' v, w} P ≫ f.complexMap

/-- In degree `0`, `f.outerComposite` sends `generatorZero x` to `1 ⊗ dψ(x)`, where `ψ` is the
section of `f.outerChoice`. -/
theorem outerComposite_zero
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋0⦌)) :
    (lichtenbaumSchlessingerComplex P').differentialIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ f.outerComposite).f 0
        (generatorZero x)) = (1 : B') ⊗ₜ D A' P'.Ring (f.outerChoice.ψ x) := by
  have e : (lichtenbaumSchlessingerComplex P).differentialIso.hom
      ((lsChainMap.{u, max u' v, w} P).f 0 (generatorZero x)) =
      (1 : B) ⊗ₜ D A P.Ring (lsSection.{u, max u' v, w} P x) :=
    (isLichtenbaumSchlessingerComparison_lsChainMap.{u, max u' v, w} P).zero x
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorZero, outerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, complexMap_f, complexMapComponent_zero, complexMapZero_apply, e,
    differentialTensorMap_tmul_D, map_one]
  rfl

/-- In degree `-1`, `f.outerComposite` sends `generatorOne x` to the image of `λ x`, where `λ`
is the linear map of `f.outerChoice`. -/
theorem outerComposite_negOne
    (x : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋1⦌)) :
    (lichtenbaumSchlessingerComplex P').freeIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ f.outerComposite).f (-1)
        (generatorOne x)) = freeQuotientToTensor P' (f.outerChoice.lam x) := by
  have e : (lichtenbaumSchlessingerComplex P).freeIso.hom
      ((lsChainMap.{u, max u' v, w} P).f (-1) (generatorOne x)) =
      freeQuotientToTensor P (lsBiderivation.{u, max u' v, w} P x) :=
    (isLichtenbaumSchlessingerComparison_lsChainMap.{u, max u' v, w} P).negOne x
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorOne, outerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, complexMap_f, complexMapComponent_negOne, complexMapOne_apply, e,
    freeTensorMap_freeQuotientToTensor]
  rfl

/-- In degree `-2`, `f.outerComposite` sends `generatorTwo g` to `1 ⊗ r(g)`, where `r` is the
relation map of `f.outerChoice`. -/
theorem outerComposite_negTwo
    (g : (CommAlgCat.standardResolution.{u, max u' v} A (CommAlgCat.of A B)).left.obj
      (op ⦋2⦌)) :
    (lichtenbaumSchlessingerComplex P').relationIso.hom
      (((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ f.outerComposite).f (-2)
        (generatorTwo g)) = (1 : B') ⊗ₜ f.outerChoice.relation g := by
  have e : (lichtenbaumSchlessingerComplex P).relationIso.hom
      ((lsChainMap.{u, max u' v, w} P).f (-2) (generatorTwo g)) =
      (1 : B) ⊗ₜ lsRelation.{u, max u' v, w} P g :=
    (isLichtenbaumSchlessingerComparison_lsChainMap.{u, max u' v, w} P).negTwo g
  rw [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
    cotangentComplexULiftIso_inv_generatorTwo, outerComposite, HomologicalComplex.comp_f,
    ConcreteCategory.comp_apply, complexMap_f, complexMapComponent_negTwo, complexMapTwo_apply, e,
    relationTensorMap_tmul, map_one]
  congr 1
  apply relationQuotientToFree_injective P'
  rw [relationQuotientToFree_relationQuotientMap, relationQuotientToFree_lsRelation,
    LichtenbaumSchlessingerRelativeChoice.relationQuotientToFree_relation]
  rfl

/-- `f.outerComposite` is given by the formulas of the relative choice `f.outerChoice`. -/
theorem isLichtenbaumSchlessingerRelativeComparison_outer :
    IsLichtenbaumSchlessingerRelativeComparison.{u, u', max u' v, w} P' f.outerChoice
      ((cotangentComplexULiftIso.{u, u', v, w} A B).inv ≫ f.outerComposite) := by
  constructor
  · intro x
    refine Eq.trans ?_ (f.outerComposite_zero x)
    rfl
  · intro x
    refine Eq.trans ?_ (f.outerComposite_negOne x)
    rfl
  · intro g
    refine Eq.trans ?_ (f.outerComposite_negTwo g)
    rfl

/-- The two composites `L_{B/A} → L'` are homotopic, hence equal in `D(B)`. -/
theorem Q_map_outerComposite :
    DerivedCategory.Q.map f.outerComposite = DerivedCategory.Q.map (innerComposite A B P') := by
  have h₁ := f.isLichtenbaumSchlessingerRelativeComparison_outer
  have h₂ := isLichtenbaumSchlessingerRelativeComparison_inner (A := A) (B := B) P'
  have H := homotopyOfIsLichtenbaumSchlessingerRelativeComparison.{u, u', max u' v, w} P' h₁ h₂
  have h := DerivedCategory.Q_map_eq_of_homotopy _ H
  rw [Functor.map_comp, Functor.map_comp] at h
  exact (cancel_epi _).1 h

/-- For a commutative square of rings `A → A'`, `B → B'` and compatible presentations `P → P'`
with `f'_t` the image of `f_t`, the canonical maps `L_{B/A} → L` and `L_{B'/A'} → L'` commute in
`D(B)` with the map `L_{B/A} → L_{B'/A'}` of cotangent complexes and the map `L → L'` of
Lichtenbaum–Schlessinger complexes, the objects over `B'` being read over `B` along `B → B'`. -/
@[stacks 09D7 "the second commutative diagram: L_{B/A} → L, L → L' equals
L_{B/A} → L_{B'/A'}, L_{B'/A'} → L' in D(B)"]
theorem canonicalCotangentToLichtenbaumSchlessinger_naturality :
    DerivedCategory.Q.map (cotangentComplexULiftSquareMap.{u, u', v, w} A A' B B') ≫
        (ModuleCat.restrictScalars (algebraMap B B')).mapDerivedCategoryFactors.inv.app
          (cotangentComplexULift.{u', max u v, w} A' B') ≫
        (ModuleCat.restrictScalars (algebraMap B B')).mapDerivedCategory.map
          (canonicalCotangentToLichtenbaumSchlessinger.{u', max u v, w} P') ≫
        (ModuleCat.restrictScalars (algebraMap B B')).mapDerivedCategoryFactors.hom.app
          (lichtenbaumSchlessingerComplex P').complex =
      canonicalCotangentToLichtenbaumSchlessinger.{u, max u' v, w} P ≫
        DerivedCategory.Q.map f.complexMap := by
  rw [canonicalCotangentToLichtenbaumSchlessinger, canonicalCotangentToLichtenbaumSchlessinger,
    cotangentToLichtenbaumSchlessinger, cotangentToLichtenbaumSchlessinger,
    Functor.mapDerivedCategoryFactors_hom_naturality, Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  have h := f.Q_map_outerComposite
  rw [outerComposite, innerComposite] at h
  exact h.symm

end LichtenbaumSchlessingerHom

end Algebra.Presentation

end
