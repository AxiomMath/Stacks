module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaUnit

/-!
# The pullback is monoidal for the tensor product sheaf, with the comparison of Tag 01CD

Let `f : X ⟶ Y` be a morphism of ringed spaces.  `Mod(𝒪_Z)` carries the monoidal structure
`SheafOfModules.monoidalCategorySheafTensor`, whose tensor product is
`Stacks.SheafOfModules.Tensor.sheafTensor Z.sheaf` and whose unit is `SheafOfModules.unit`
definitionally.  This file makes `f^*` a monoidal functor for that structure, with the comparison
`c_{A,B} : f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of [Stacks, Tag 01CD] as its oplax tensorator and the
comparison `ν : f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves as its oplax unit.

## Main definitions

* `Stacks.PullbackSheafTensor.sheafTensorComparison`: `Stacks.RingedSpace.comparison`, with its
  source and target ascribed at the monoidal product `⊗` of the re-seated structure.
* `Stacks.PullbackSheafTensor.coreMonoidal` and `monoidal`: **`f^*` as a monoidal functor for the
  re-seated structure, whose oplax tensorator is the comparison of [Stacks, Tag 01CD] and whose
  oplax unit is `ν`.**

## Main results

* `Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_left` and `..._naturality_right`:
  naturality of the comparison in each variable, in whiskered form.
* `Stacks.PullbackSheafTensor.sheafTensorComparison_associator`: **the comparison of
  [Stacks, Tag 01CD] is compatible with the associator of the re-seated structure.**
* `Stacks.PullbackSheafTensor.sheafTensorComparison_leftUnitor` and `..._rightUnitor`: the
  comparison is compatible with the two unitors, the unit object being matched by `ν`.
* `Stacks.PullbackSheafTensor.delta_monoidal` and `epsilon_monoidal`: the oplax tensorator of
  `monoidal` is the comparison and its lax unit is `ν⁻¹`, by construction.

## Implementation notes

**The ascription is what makes the whiskerings rewritable.**  The source of
`Stacks.RingedSpace.comparison` is spelled `f^*((tensorSheaf Y).obj (A, B))`, and `A ⊗ B` for the
re-seated structure is a different term equal to it by `rfl`.  A composite mixing the two is not
type-correct at `implicit` transparency, so `rw` refuses a goal containing it and reports a
missing pattern rather than the cause.  `sheafTensorComparison` is the comparison with its type
ascribed at the `⊗` spelling, every statement below uses it, and the crossing happens once per
lemma inside a defeq-tolerant `:=`.  This is the cure prescribed for `tmul` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence`, applied to the
comparison.

**Where the associativity coherence comes from.**  It is
`Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator`, the same coherence for
`Stacks.PullbackGradedAlgebra.monoidalCategory`, transported across the identifications of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictSheafTensorAgree`.  The two
structures have the same tensor product on objects. Their associators agree by the generic
conjugation comparison `Stacks.RingedSpace.associator_eq_strict`, and
`sheafTensorComparison_whiskerLeft_eq_strict` and `..._whiskerRight_eq_strict` identify the two
whiskerings.

**Neither structure is left to instance synthesis.**  `Mod(𝒪_Z)` carries the re-seated structure
and `Stacks.PullbackGradedAlgebra.monoidalCategory` at once, and the latter is stated over
`Stacks.RingedSpace.structureRingSheaf`, which instance search cannot recover.  The re-seated
one is named here by the `@[instance_reducible] local instance` `monoidalSheafTensor`, and every
statement mentioning the other one names it by `@`-application.

## References

* [The Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [The Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.RingedSpace

universe u

namespace Stacks.PullbackSheafTensor

/-- The monoidal structure on `Mod(𝒪_Z)` whose tensor product is the tensor product sheaf of
[Stacks, Tag 01CA], named so that the notation `⊗`, `◁`, `▷`, `α_`, `λ_`, `ρ_` below refers to
it and not to `Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
@[instance_reducible] local instance monoidalSheafTensor (Z : RingedSpace.{u, u}) :
    MonoidalCategory (_root_.SheafOfModules.{u} (structureRingSheaf Z)) :=
  _root_.SheafOfModules.monoidalCategorySheafTensor Z.sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-! ### The comparison of Tag 01CD at the re-seated monoidal spelling -/

/-- **The comparison of [Stacks, Tag 01CD]**, `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`, with source and target
spelled through the monoidal product of the re-seated structure. -/
def sheafTensorComparison (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj (A ⊗ B) ⟶
      (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B :=
  comparison f A B

/-- The comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` is an isomorphism. -/
instance isIso_sheafTensorComparison
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    IsIso (sheafTensorComparison f A B) :=
  Stacks.PullbackTensor.isIso_comparison f A B

/-- **The comparison of [Stacks, Tag 01CD] as an isomorphism** at the re-seated monoidal
spelling. -/
def sheafTensorComparisonIso (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj (A ⊗ B) ≅
      (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B :=
  asIso (sheafTensorComparison f A B)

/-- The forward morphism of `sheafTensorComparisonIso` is `sheafTensorComparison`. -/
theorem sheafTensorComparisonIso_hom
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (sheafTensorComparisonIso f A B).hom = sheafTensorComparison f A B :=
  rfl

/-- **The comparison `ν : f^*𝒪_Y ≅ 𝒪_X` of the structure sheaves**, with its source and target
ascribed at the unit object `𝟙_` of the re-seated structure.  The ascription is needed for the
same reason as for `sheafTensorComparison`. -/
def sheafTensorUnitIso :
    (pullbackFunctor f).obj (𝟙_ (_root_.SheafOfModules.{u} (structureRingSheaf Y))) ≅
      𝟙_ (_root_.SheafOfModules.{u} (structureRingSheaf X)) :=
  pullbackObjUnitIso f

/-! ### Naturality in each variable -/

/-- Naturality of the comparison at `(v, w)`, with the two tensored morphisms given by `m`, `m'`. -/
private theorem sheafTensorComparison_naturality_aux
    {A A' B B' : _root_.SheafOfModules.{u} (structureRingSheaf Y)} (v : A ⟶ A') (w : B ⟶ B')
    (m : A ⊗ B ⟶ A' ⊗ B') (m' : (pullbackFunctor f).obj A ⊗ (pullbackFunctor f).obj B ⟶
      (pullbackFunctor f).obj A' ⊗ (pullbackFunctor f).obj B')
    (hm : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      Y.sheaf)).map (X := (A, B)) (Y := (A', B')) (v, w) = m)
    (hm' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      X.sheaf)).map (X := ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B))
        (Y := ((pullbackFunctor f).obj A', (pullbackFunctor f).obj B'))
        ((pullbackFunctor f).map v, (pullbackFunctor f).map w) = m') :
    sheafTensorComparison f A B ≫ m' =
      (pullbackFunctor f).map m ≫ sheafTensorComparison f A' B' := by
  subst hm hm'
  exact ((comparisonNatTrans f).naturality ((v, w) : (A, B) ⟶ (A', B'))).symm

/-- **Naturality of the comparison in the first variable**, in whiskered form: the whiskering of
the re-seated structure is the action of the tensor product sheaf on a morphism, so this is the
naturality square of `Stacks.RingedSpace.comparisonNatTrans` at `v ×ₘ 𝟙`. -/
theorem sheafTensorComparison_naturality_left
    {A A' : _root_.SheafOfModules.{u} (structureRingSheaf Y)} (v : A ⟶ A')
    (B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    sheafTensorComparison f A B ≫ ((pullbackFunctor f).map v ▷ (pullbackFunctor f).obj B) =
      (pullbackFunctor f).map (v ▷ B) ≫ sheafTensorComparison f A' B :=
  sheafTensorComparison_naturality_aux f v (𝟙 B) _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Y.sheaf v (𝟙 B)).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_map_app Y.sheaf v B).symm)
    (by
      rw [CategoryTheory.Functor.map_id]
      exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf _ _).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_map_app X.sheaf _ _).symm)

/-- **Naturality of the comparison in the second variable**, in whiskered form. -/
theorem sheafTensorComparison_naturality_right
    (A : _root_.SheafOfModules.{u} (structureRingSheaf Y))
    {B B' : _root_.SheafOfModules.{u} (structureRingSheaf Y)} (w : B ⟶ B') :
    sheafTensorComparison f A B ≫ ((pullbackFunctor f).obj A ◁ (pullbackFunctor f).map w) =
      (pullbackFunctor f).map (A ◁ w) ≫ sheafTensorComparison f A B' :=
  sheafTensorComparison_naturality_aux f (𝟙 A) w _ _
    ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map Y.sheaf (𝟙 A) w).trans
      (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map Y.sheaf A w).symm)
    (by
      rw [CategoryTheory.Functor.map_id]
      exact (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf _ _).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map X.sheaf _ _).symm)

/-! ### Compatibility with the associator -/

/-- `sheafTensorComparison` is `Stacks.PullbackTensorCoherence.pullbackTensorComparison`, the two
differing only in how their source and target are spelled. -/
theorem sheafTensorComparison_eq_strict
    (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    sheafTensorComparison f A B =
      Stacks.PullbackTensorCoherence.pullbackTensorComparison f A B :=
  rfl

/-- The comparison left-whiskered in the re-seated structure is the comparison left-whiskered in
`Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
theorem sheafTensorComparison_whiskerLeft_eq_strict
    (A B D : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).obj A ◁ sheafTensorComparison f B D =
      @MonoidalCategoryStruct.whiskerLeft _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct
        ((pullbackFunctor f).obj A) _ _
        (Stacks.PullbackTensorCoherence.pullbackTensorComparison f B D) :=
  whiskerLeft_eq_strict ((pullbackFunctor f).obj A) (sheafTensorComparison f B D)

/-- The comparison right-whiskered in the re-seated structure is the comparison right-whiskered
in `Stacks.PullbackGradedAlgebra.monoidalCategory`. -/
theorem sheafTensorComparison_whiskerRight_eq_strict
    (A B D : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    sheafTensorComparison f A B ▷ (pullbackFunctor f).obj D =
      @MonoidalCategoryStruct.whiskerRight _ _
        (Stacks.PullbackGradedAlgebra.monoidalCategory X).toMonoidalCategoryStruct _ _
        (Stacks.PullbackTensorCoherence.pullbackTensorComparison f A B)
        ((pullbackFunctor f).obj D) :=
  whiskerRight_eq_strict (sheafTensorComparison f A B) ((pullbackFunctor f).obj D)

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the associator of the re-seated
structure.**  The two monoidal structures on `Mod(𝒪_Z)` have the same tensor product on objects
and the same associator, so the coherence for
`Stacks.PullbackGradedAlgebra.monoidalCategory` becomes this one once the two whiskerings are
moved across. -/
theorem sheafTensorComparison_associator
    (A B D : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).map (α_ A B D).hom ≫ sheafTensorComparison f A (B ⊗ D) ≫
        ((pullbackFunctor f).obj A ◁ sheafTensorComparison f B D) =
      sheafTensorComparison f (A ⊗ B) D ≫
        (sheafTensorComparison f A B ▷ (pullbackFunctor f).obj D) ≫
          (α_ ((pullbackFunctor f).obj A) ((pullbackFunctor f).obj B)
            ((pullbackFunctor f).obj D)).hom := by
  have sourceAssociator := associator_eq_strict (Z := Y) A B D
  have targetAssociator := associator_eq_strict (Z := X) ((pullbackFunctor f).obj A)
    ((pullbackFunctor f).obj B) ((pullbackFunctor f).obj D)
  refine (congrArg₂ (· ≫ ·) (congrArg (pullbackFunctor f).map sourceAssociator)
    (congrArg₂ (· ≫ ·) rfl (sheafTensorComparison_whiskerLeft_eq_strict f A B D))).trans ?_
  refine (Stacks.PullbackTensorCoherence.pullbackTensorComparison_associator f A B D).trans ?_
  exact congrArg₂ (· ≫ ·) rfl (congrArg₂ (· ≫ ·)
    (sheafTensorComparison_whiskerRight_eq_strict f A B D).symm targetAssociator.symm)

/-! ### Compatibility with the unitors -/

/-- Rewriting the middle and last factors of a composite by equations. -/
private theorem eq_comp_comp_of_eq {C : Type*} [Category C] {P Q R S : C} {g : P ⟶ S} {c : P ⟶ Q}
    {T w : Q ⟶ R} {t u : R ⟶ S} (h : g = c ≫ T ≫ t) (hT : T = w) (hu : u = t) :
    g = c ≫ w ≫ u := by
  rw [h, hT, hu]

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the left unitor of the re-seated
structure**, the unit object being matched by `ν : f^*𝒪_Y ≅ 𝒪_X`.  The unitors of the re-seated
structure are the unitors of the tensor product sheaf, for which this is the left-unitor
coherence of [Stacks, Tag 01CD]. -/
theorem sheafTensorComparison_leftUnitor
    (M : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).map (λ_ M).hom =
      sheafTensorComparison f (𝟙_ (_root_.SheafOfModules.{u} (structureRingSheaf Y))) M ≫
        ((sheafTensorUnitIso f).hom ▷ (pullbackFunctor f).obj M) ≫
          (λ_ ((pullbackFunctor f).obj M)).hom :=
  eq_comp_comp_of_eq
    ((congrArg (pullbackFunctor f).map (leftUnitor_sheafTensor_eq Y M)).trans
      (comparison_leftUnitor f M).symm)
    ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf
      (sheafTensorUnitIso f).hom (𝟙 ((pullbackFunctor f).obj M))).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_map_app X.sheaf
          (sheafTensorUnitIso f).hom ((pullbackFunctor f).obj M)).symm)
    (leftUnitor_sheafTensor_eq X ((pullbackFunctor f).obj M))

/-- **The comparison of [Stacks, Tag 01CD] is compatible with the right unitor of the re-seated
structure**, obtained the same way. -/
theorem sheafTensorComparison_rightUnitor
    (M : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    (pullbackFunctor f).map (ρ_ M).hom =
      sheafTensorComparison f M (𝟙_ (_root_.SheafOfModules.{u} (structureRingSheaf Y))) ≫
        ((pullbackFunctor f).obj M ◁ (sheafTensorUnitIso f).hom) ≫
          (ρ_ ((pullbackFunctor f).obj M)).hom :=
  eq_comp_comp_of_eq
    ((congrArg (pullbackFunctor f).map (rightUnitor_sheafTensor_eq Y M)).trans
      (comparison_rightUnitor f M).symm)
    ((Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map X.sheaf
      (𝟙 ((pullbackFunctor f).obj M)) (sheafTensorUnitIso f).hom).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_obj_map X.sheaf
          ((pullbackFunctor f).obj M) (sheafTensorUnitIso f).hom).symm)
    (rightUnitor_sheafTensor_eq X ((pullbackFunctor f).obj M))

/-! ### The pullback as a monoidal functor for the tensor product sheaf -/

/-- **`f^*` is a monoidal functor for the monoidal structure whose tensor product is the tensor
product sheaf, with the comparison of [Stacks, Tag 01CD] as its oplax tensorator**: this is
`CategoryTheory.Functor.CoreMonoidal.mk'` applied to the two naturality statements and the three
coherences above. -/
def coreMonoidal : (pullbackFunctor f).CoreMonoidal :=
  Functor.CoreMonoidal.mk'
    (εIso := (sheafTensorUnitIso f).symm)
    (μIso := fun A B ↦ (sheafTensorComparisonIso f A B).symm)
    (μIso_inv_natural_left := fun v B ↦ sheafTensorComparison_naturality_left f v B)
    (μIso_inv_natural_right := fun A w ↦ sheafTensorComparison_naturality_right f A w)
    (oplax_associativity := fun A B D ↦ (sheafTensorComparison_associator f A B D).symm)
    (oplax_left_unitality := fun M ↦ by
      rw [← cancel_mono (λ_ ((pullbackFunctor f).obj M)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, sheafTensorComparisonIso_hom]
      rw [← sheafTensorComparison_leftUnitor, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id])
    (oplax_right_unitality := fun M ↦ by
      rw [← cancel_mono (ρ_ ((pullbackFunctor f).obj M)).hom, Iso.inv_hom_id, Category.assoc,
        Category.assoc]
      simp only [Iso.symm_inv, sheafTensorComparisonIso_hom]
      rw [← sheafTensorComparison_rightUnitor, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id])

/-- The monoidal functor structure on `f^*` for the tensor product sheaf.  Deliberately **not** a
global instance: `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` is a second
`CategoryTheory.Functor.Monoidal` structure on the same functor, at a second monoidal structure
on `Mod(𝒪_Z)`, and registering both would make instance search choose between them silently. -/
@[instance_reducible]
def monoidal : (pullbackFunctor f).Monoidal :=
  (coreMonoidal f).toMonoidal

/-- The oplax tensorator of `monoidal` is the comparison of [Stacks, Tag 01CD], by
construction. -/
theorem delta_monoidal (A B : _root_.SheafOfModules.{u} (structureRingSheaf Y)) :
    Functor.OplaxMonoidal.δ (self := (monoidal f).toOplaxMonoidal) (pullbackFunctor f) A B =
      comparison f A B :=
  rfl

/-- The lax unit of `monoidal` is the inverse of `ν : f^*𝒪_Y ≅ 𝒪_X`, by construction; equivalently
its oplax unit is `ν`. -/
theorem epsilon_monoidal :
    Functor.LaxMonoidal.ε (self := (monoidal f).toLaxMonoidal) (pullbackFunctor f) =
      (RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f).inv :=
  rfl

end Stacks.PullbackSheafTensor

end
