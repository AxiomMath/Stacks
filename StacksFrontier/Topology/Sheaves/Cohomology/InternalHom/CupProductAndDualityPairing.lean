module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedApplicationUnitLaw
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom

/-!
# Cup product with a class in `H⁰(X, K ⊗^L E^∨)` and the evaluation of the dual

Let `(X, O_X)` be a ringed space and let `K` and `E` be objects of `D(O_X)` with `E` perfect.
Write `E^∨ = RSheafHom(E, O_X)` for the dual and let `ε : E^∨ ⊗^L_{O_X} E ⟶ O_X` be the
evaluation map. Stacks 0FVB asserts that the square whose top arrow is the cup product

`H⁰(X, K ⊗^L E^∨) × H⁰(X, E) ⟶ H⁰(X, K ⊗^L E^∨ ⊗^L E)`,

whose right arrow is induced by `ε`, whose left arrow is the identification
`H⁰(X, K ⊗^L E^∨) = Hom_{D(O_X)}(E, K)` of Stacks 08DQ and whose bottom arrow evaluates a
morphism `E ⟶ K` on a class in `H⁰(X, E)` commutes.

Degree-zero global hypercohomology is read throughout as morphisms out of the structure sheaf:
a class in `H⁰(X, Z)` is a morphism `O_X ⟶ Z` in `D(O_X)`. In that reading the cup product of
two classes is the tensor product of their morphisms preceded by the left unitor
`O_X ≅ O_X ⊗^L_{O_X} O_X` (Stacks 0FP2), the bottom arrow is precomposition, and the
commutativity of the square is the identity proved below.

## Main definitions

* `Stacks.SheafOfModules.derivedDualContraction`: the morphism `(K ⊗^L E^∨) ⊗^L E ⟶ K` obtained
  by re-bracketing, evaluating `ε` on the last two factors and removing the unit factor. The
  right vertical arrow of Stacks 0FVB is its degree-zero global hypercohomology.
* `Stacks.SheafOfModules.derivedSectionTensor`: the cup product of two global sections in the
  form of Stacks 0FP2, the tensor product of the two morphisms out of the structure sheaf
  preceded by the left unitor.
* `Stacks.SheafOfModules.derivedDualSectionToHom`: the morphism `E ⟶ K` attached to a morphism
  `O_X ⟶ K ⊗^L E^∨`, namely the left unitor followed by a whiskering and the contraction above.

## Main results

* `Stacks.SheafOfModules.derivedSectionTensor_comp_derivedDualContraction`: contracting the cup
  product of `ξ : O_X ⟶ K ⊗^L E^∨` and `η : O_X ⟶ E` against `ε` is `η` followed by the
  morphism `E ⟶ K` attached to `ξ`.
* `Stacks.SheafOfModules.derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom`: the
  identification `H⁰(X, K ⊗^L E^∨) ⟶ Hom_{D(O_X)}(E, K)` of Stacks 08I1 is the morphism
  attached to a class by `derivedDualSectionToHom`, as soon as the canonical map of Stacks 08I1
  followed by the application morphism of Stacks 08J8 is the contraction against `ε` and the
  unit law tying Stacks 08JA to Stacks 08J8 holds; the second is
  `Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal`, which gives
  `derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom_of_applicationLaw`.
* `Stacks.SheafOfModules.derivedStructureSheafGlobalSectionsEquiv_derivedDualContraction`: the
  first result read through the identification `H⁰(X, Z) = Hom_{D(O_X)}(O_X, Z)` on the right
  vertical arrow.

The square of Stacks 0FVB itself is `Stacks.SheafOfModules.derivedDualPairingSquare`.

## Implementation notes

The monoidal structure is `Stacks.SheafOfModules.derivedMonoidalStructure` of Stacks 0FPT, whose
tensor product is `Stacks.SheafOfModules.derivedTensor` and whose unit is the structure sheaf in
degree zero; the associator, the unitors and the whiskerings below are those of the derived
tensor product. The source writes `K ⊗^L E^∨ ⊗^L E` without brackets; the bracketing used here
is `(K ⊗^L E^∨) ⊗^L E`.

The evaluation map is `AlgebraicGeometry.RingedSite.derivedDualEvaluation`, the morphism matched
with the identity of `E^∨` by the tensor–internal-Hom bijection of Stacks 08J8; it is the
application morphism of Stacks 08J8 at target `O_X`
(`Stacks.SheafOfModules.derivedSheafHomCounit_structureSheaf_eq_derivedDualEvaluation`).

A class of `H⁰(X, Z)` is a morphism `O_X ⟶ Z` in `D(O_X)` through
`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`, which is natural in `Z`
(`AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality`). In that
reading the cup product of two classes is the tensor product of their morphisms preceded by the
left unitor `O_X ≅ O_X ⊗^L_{O_X} O_X` (Stacks 0FP2).

## References

* [Stacks Project, Tag 0FVB](https://stacks.math.columbia.edu/tag/0FVB)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 0FP2](https://stacks.math.columbia.edu/tag/0FP2)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

attribute [local implicit_reducible] CategoryTheory.sheafCompose Tensor.ringSheaf

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- **The cup product of two global sections.** For morphisms `x : O_X ⟶ A` and `y : O_X ⟶ B` in
`D(O_X)`, which is what classes in `H⁰(X, A)` and `H⁰(X, B)` are, their cup product is the
morphism `O_X ⟶ A ⊗^L_{O_X} B` given by the left unitor `O_X ≅ O_X ⊗^L_{O_X} O_X` followed by
`x ⊗ y`. This is the description of the cup product in Stacks 0FP2. -/
def derivedSectionTensor {A B : DerivedCategory (StructureSheafModules Rc)}
    (x : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ A)
    (y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ B) :
    𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ ((derivedTensor Rc).obj A).obj B :=
  (λ_ (𝟙_ (DerivedCategory (StructureSheafModules Rc)))).inv ≫ (x ⊗ₘ y)

/-- The cup product of two global sections is the second one followed by the left unitor and the
whiskering of the first one. -/
private lemma derivedSectionTensor_eq {A B : DerivedCategory (StructureSheafModules Rc)}
    (x : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ A)
    (y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ B) :
    derivedSectionTensor Rc x y = y ≫ (λ_ B).inv ≫ (x ▷ B) := by
  have h : derivedSectionTensor Rc x y =
      (λ_ (𝟙_ (DerivedCategory (StructureSheafModules Rc)))).inv ≫ (x ⊗ₘ y) := rfl
  rw [h, tensorHom_def', leftUnitor_inv_naturality_assoc]

/-- The map induced on `H⁰` by `f : Z ⟶ W` sends the class of `x : O_X ⟶ Z` to the class of
`x ≫ f`. -/
private lemma homologyMap_derivedModuleGlobalSections_symm
    {Z W : DerivedCategory (StructureSheafModules Rc)} (f : Z ⟶ W)
    (x : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ Z) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections (ringedSite Rc)).map f)
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) Z).symm x) =
      (RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) W).symm (x ≫ f) := by
  rw [AddEquiv.eq_symm_apply, RingedSite.derivedStructureSheafGlobalSectionsEquiv_naturality,
    AddEquiv.apply_symm_apply]

variable (K E : DerivedCategory (StructureSheafModules Rc))

/-- **Contraction of a dual factor.** The morphism

`(K ⊗^L_{O_X} E^∨) ⊗^L_{O_X} E ⟶ K`

in `D(O_X)` which re-brackets, evaluates `ε : E^∨ ⊗^L_{O_X} E ⟶ O_X` on the last two factors and
removes the resulting unit factor. The right vertical arrow of Stacks 0FVB is its degree-zero
global hypercohomology. -/
def derivedDualContraction :
    ((derivedTensor Rc).obj (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).obj E ⟶ K :=
  (α_ K (derivedDual Rc E) E).hom ≫
    (K ◁ RingedSite.derivedDualEvaluation (ringedSite Rc) E) ≫ (ρ_ K).hom

/-- **The morphism `E ⟶ K` attached to a global section of `K ⊗^L_{O_X} E^∨`.** For
`x : O_X ⟶ K ⊗^L_{O_X} E^∨` it is the composition

`E = O_X ⊗^L_{O_X} E ⟶ (K ⊗^L_{O_X} E^∨) ⊗^L_{O_X} E ⟶ K`

of the left unitor, the whiskering of `x` by `E`, and
`Stacks.SheafOfModules.derivedDualContraction`. This is the morphism the proof of Stacks 0FVB
identifies the left vertical arrow with. -/
def derivedDualSectionToHom
    (x : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedTensor Rc).obj K).obj (derivedDual Rc E)) :
    E ⟶ K :=
  (λ_ E).inv ≫ (x ▷ E) ≫ derivedDualContraction Rc K E

variable [∀ V : Opens X, HasSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]
  [∀ V : Opens X, ((Opens.grothendieckTopology X).over V).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [∀ V : Opens X, HasWeakSheafify ((Opens.grothendieckTopology X).over V) AddCommGrpCat.{u}]

/-- **Contracting a cup product against the evaluation of the dual.** Let `(X, O_X)` be a ringed
space, let `K` and `E` be objects of `D(O_X)` with `E` perfect, and let
`ξ : O_X ⟶ K ⊗^L_{O_X} E^∨` and `η : O_X ⟶ E`. Contracting the cup product of `ξ` and `η`
against the evaluation of the dual gives the same morphism `O_X ⟶ K` as evaluating on `η` the
morphism `E ⟶ K` attached to `ξ`:

`(1_K ⊗ ε) ∘ (ξ ⊗ η) = (1_K ⊗ ε) ∘ (ξ ⊗ 1_E) ∘ (1_O ⊗ η)`. -/
theorem derivedSectionTensor_comp_derivedDualContraction
    (hE : (ringedSite Rc).IsPerfect E)
    (ξ : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedTensor Rc).obj K).obj (derivedDual Rc E))
    (η : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ E) :
    derivedSectionTensor Rc ξ η ≫ derivedDualContraction Rc K E =
      η ≫ derivedDualSectionToHom Rc K E ξ := by
  have := hE
  have h : derivedDualSectionToHom Rc K E ξ =
      (λ_ E).inv ≫ (ξ ▷ E) ≫ derivedDualContraction Rc K E := rfl
  rw [derivedSectionTensor_eq, h]
  simp only [Category.assoc]

/-- **The identification of Stacks 08I1 on a class, from two equations about canonical
morphisms.** Write `Φ = derivedTensorDualToSheafHom Rc E K` for the canonical map of
Stacks 08I1 and `app = derivedSheafHomCounit Rc E K` for the application morphism
`RSheafHom(E, K) ⊗^L_{O_X} E ⟶ K` of Stacks 08J8. If

* `happ`: `(Φ ▷ E) ≫ app = derivedDualContraction Rc K E`, and
* `hunit`: for every `y : O_X ⟶ RSheafHom(E, K)` the morphism `E ⟶ K` that `y` names under the
  two identifications of Stacks 08JA is `(λ_E)⁻¹` followed by `y ▷ E` and application,

then the identification `H⁰(X, K ⊗^L E^∨) ⟶ Hom_{D(O_X)}(E, K)` of Stacks 08I1 sends the class
of `ξ : O_X ⟶ K ⊗^L E^∨` to `(λ_E)⁻¹ ≫ (ξ ▷ E) ≫ derivedDualContraction Rc K E`. -/
theorem derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom
    (happ : derivedTensorDualToSheafHom Rc E K ▷ E ≫ derivedSheafHomCounit Rc E K =
      derivedDualContraction Rc K E)
    (hunit : ∀ y : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
        ((derivedSheafHom Rc).obj (op E)).obj K,
      y ▷ E ≫ derivedSheafHomCounit Rc E K =
        (λ_ E).hom ≫ derivedSheafHomGlobalSectionsEquiv Rc E K
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedSheafHom Rc).obj (op E)).obj K)).symm y))
    (ξ : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedTensor Rc).obj K).obj (derivedDual Rc E)) :
    derivedTensorDualGlobalSectionsMap Rc E K
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).symm ξ) =
      derivedDualSectionToHom Rc K E ξ := by
  -- The unit law at the class of `ξ ≫ Φ`, with `happ` collapsing the second leg.
  have hmain := hunit (ξ ≫ derivedTensorDualToSheafHom Rc E K)
  rw [comp_whiskerRight, Category.assoc, happ] at hmain
  -- Cancel the left unitor in the hypothesis.
  have hmain' := congrArg (fun g => (λ_ E).inv ≫ g) hmain
  simp only [Iso.inv_hom_id_assoc] at hmain'
  rw [derivedTensorDualGlobalSectionsMap_apply,
    homologyMap_derivedModuleGlobalSections_symm, ← hmain']
  rfl

/-- **Contracting a cup product against the evaluation of the dual, on `H⁰`.** Let `(X, O_X)`
be a ringed space, let `K` and `E` be objects of `D(O_X)` with `E` perfect, and let
`ξ : O_X ⟶ K ⊗^L_{O_X} E^∨` and `η : O_X ⟶ E`. Applying to the class of the cup product of `ξ`
and `η` in `H⁰(X, (K ⊗^L E^∨) ⊗^L E)` the map induced on `H⁰` by the contraction against `ε`
gives the class of `H⁰(X, K)` of the morphism obtained by evaluating on `η` the morphism
`E ⟶ K` attached to `ξ`. -/
theorem derivedStructureSheafGlobalSectionsEquiv_derivedDualContraction
    (hE : (ringedSite Rc).IsPerfect E)
    (ξ : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedTensor Rc).obj K).obj (derivedDual Rc E))
    (η : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶ E) :
    RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc) K
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections (ringedSite Rc)).map
            (derivedDualContraction Rc K E))
          ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
            (((derivedTensor Rc).obj
              (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).obj E)).symm
              (derivedSectionTensor Rc ξ η))) =
      η ≫ derivedDualSectionToHom Rc K E ξ := by
  rw [homologyMap_derivedModuleGlobalSections_symm, AddEquiv.apply_symm_apply]
  exact derivedSectionTensor_comp_derivedDualContraction Rc K E hE ξ η

/-- **The identification of Stacks 08I1 on a class, from the first equation.** If the canonical
map of Stacks 08I1 followed by the application morphism of Stacks 08J8 is the contraction
against `ε`, then the identification `H⁰(X, K ⊗^L E^∨) ⟶ Hom_{D(O_X)}(E, K)` sends the class of
`ξ : O_X ⟶ K ⊗^L E^∨` to `(λ_E)⁻¹ ≫ (ξ ▷ E) ≫ derivedDualContraction Rc K E`; the unit law is
`Stacks.SheafOfModules.derivedSheafHomCounit_unit_law_monoidal`. -/
theorem derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom_of_applicationLaw
    (happ : derivedTensorDualToSheafHom Rc E K ▷ E ≫ derivedSheafHomCounit Rc E K =
      derivedDualContraction Rc K E)
    (ξ : 𝟙_ (DerivedCategory (StructureSheafModules Rc)) ⟶
      ((derivedTensor Rc).obj K).obj (derivedDual Rc E)) :
    derivedTensorDualGlobalSectionsMap Rc E K
        ((RingedSite.derivedStructureSheafGlobalSectionsEquiv (ringedSite Rc)
          (((derivedTensor Rc).obj K).obj (derivedDual Rc E))).symm ξ) =
      derivedDualSectionToHom Rc K E ξ :=
  derivedTensorDualGlobalSectionsMap_eq_derivedDualSectionToHom Rc K E happ
    (derivedSheafHomCounit_unit_law_monoidal Rc E K) ξ

end Stacks.SheafOfModules

end
