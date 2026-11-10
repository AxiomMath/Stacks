module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupBaseShiftPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupProductAdjunctFormula
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaShiftedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointUnitalComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The cup product with the universal class of a degree

Let `(S, 𝒪_S)` be a ringed space, `A = Γ(S, 𝒪_S)` and let `L ⊣ RΓ(S, -)` be the adjunction of the
canonical one-point comparison from which the global cup product of Cohomology, Section 0FKU is
built. For an integer `i` the object `Z₀ = L(A[-i])` of `D(𝒪_S)` carries the class `z₀ ∈ Hⁱ(S, Z₀)`
of the unit `A[-i] ⟶ RΓ(S, L(A[-i]))`, and `z₀` is *universal*: every class `ξ ∈ Hⁱ(S, Z)` is
`Hⁱ(g)(z₀)` for exactly one morphism `g : Z₀ ⟶ Z`. This file proves that the cup product with
`z₀` is bijective,

`z₀ ∪ - : Hʲ(S, E) ⟶ Hⁱ⁺ʲ(S, Z₀ ⊗^𝐋 E)`, for every `E ∈ D(𝒪_S)` and all `i, j`.

This reduces a pairing defined by the cup product in degrees `(i, j)` to a morphism out of
`Z₀ ⊗^𝐋 E`, which is how [Stacks, Tag 0FVY] is proved.

The proof: `z₀ ∪ η` is the class of `pinnedSplitting` followed by `A[-i] ⊗ η` and the relative cup
product of Tag 0B68 at `(Z₀, E)` precomposed with the unit (Section 0FKU read through Tag 06XS);
the splitting is invertible and so is the comparison of bifunctors of the canonical one-point
comparison (`CupProductAdjunctFormula`); and composition with the relative cup product of the unit
is a bijection as soon as tensoring by `Z₀` is fully faithful, which holds because `Z₀` is a shift
of the unit object (`bijective_map_tensorPullbackBaseShift`).

Standard model: uses `Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`,
`Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing` and `pinnedSplitting`, which exist only
there.

## Main definitions

* `Stacks.Cohomology.DerivedGlobalCupProduct.cupUniversalObject` — the object `Z₀ = L(A[-i])`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupUniversalClass` — the class `z₀ ∈ Hⁱ(S, Z₀)`.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.map_unit_comp_adjunctionBitensorMap` — the
  abstract relative cup product of Tag 0B68, precomposed with the unit in the first factor, is the
  adjoint transpose of the comparison followed by the transpose in the second factor.
* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_cupUniversalClass_comp` — the universal
  property of `z₀`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.bijective_cupUniversalClass_cupPairing_canonical` —
  **the cup product with `z₀` is bijective.**

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 0FVY](https://stacks.math.columbia.edu/tag/0FVY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedRelativeCupProduct

section Abstract

variable {C : Type*} {D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
  (adj : L ⊣ R) (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- **The relative cup product with the unit in the first factor.** For `P, T : C`, `G : D` and
`s : T ⟶ R G`, tensoring `s` with `P`, then the unit of `L ⊣ R` at `P` with `R G`, then the
abstract relative cup product of Tag 0B68 at `(L P, G)`, is the adjoint transpose of the comparison
`α` at `(P, T)` followed by `B` of the identity of `L P` and the transpose of `s`. -/
lemma map_unit_comp_adjunctionBitensorMap (P T : C) (G : D) (s : T ⟶ R.obj G) :
    A.map (𝟙 P ×ₘ s) ≫ A.map (adj.unit.app P ×ₘ 𝟙 (R.obj G)) ≫
        adjunctionBitensorMap adj A B α (L.obj P) G =
      adj.homEquiv _ _ (α.app (P, T) ≫ B.map (𝟙 (L.obj P) ×ₘ (adj.homEquiv _ _).symm s)) := by
  apply (adj.homEquiv _ _).symm.injective
  have hα := α.naturality (X := (P, T)) (Y := (R.obj (L.obj P), R.obj G))
    (adj.unit.app P ×ₘ s)
  simp only [Functor.comp_map, Functor.prod_map] at hα
  simp only [Equiv.symm_apply_apply, adjunctionBitensorMap,
    Adjunction.homEquiv_naturality_left_symm, Functor.comp_obj]
  rw [← Functor.map_comp_assoc, ← A.map_comp, prod_comp, Category.id_comp, Category.comp_id,
    reassoc_of% hα, ← B.map_comp, prod_comp, adj.left_triangle_components,
    Adjunction.homEquiv_counit]

/-- **Composition with the relative cup product of the unit is a bijection**, when `α` is
invertible at `(P, T)` and `B(L P, -)` is fully faithful. -/
lemma bijective_map_unit_comp_adjunctionBitensorMap (P T : C) (G : D)
    (hα : IsIso (α.app (P, T)))
    (hB : ∀ M M' : D, Function.Bijective (fun v : M ⟶ M' ↦ B.map (𝟙 (L.obj P) ×ₘ v))) :
    Function.Bijective (fun s : T ⟶ R.obj G ↦ A.map (𝟙 P ×ₘ s) ≫
        A.map (adj.unit.app P ×ₘ 𝟙 (R.obj G)) ≫ adjunctionBitensorMap adj A B α (L.obj P) G) := by
  have h : (fun s : T ⟶ R.obj G ↦ A.map (𝟙 P ×ₘ s) ≫
        A.map (adj.unit.app P ×ₘ 𝟙 (R.obj G)) ≫ adjunctionBitensorMap adj A B α (L.obj P) G) =
      (adj.homEquiv _ _) ∘ (fun w ↦ α.app (P, T) ≫ w) ∘
        (fun v : L.obj T ⟶ G ↦ B.map (𝟙 (L.obj P) ×ₘ v)) ∘ (adj.homEquiv _ _).symm := by
    funext s
    exact map_unit_comp_adjunctionBitensorMap adj A B α P T G s
  rw [h]
  refine (adj.homEquiv _ _).bijective.comp (Function.Bijective.comp ?_
    ((hB _ _).comp (adj.homEquiv _ _).symm.bijective))
  exact (isIso_iff_coyoneda_map_bijective _).1 hα _

end Abstract

end Stacks.Cohomology.DerivedRelativeCupProduct

namespace Stacks.Cohomology.DerivedGlobalCupProduct

open Stacks.Cohomology.GlobalKunneth

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf CategoryTheory.sheafCompose
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable (S : RingedSpace.{u, u})

/-- **The universal object of degree `i`**, `Z₀ = L(A[-i])` for the left adjoint `L` of derived
global sections of the canonical one-point comparison and `A = Γ(S, 𝒪_S)`. -/
abbrev cupUniversalObject (i : ℤ) : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) :=
  (onePointComparisonCanonical S).pullback.obj (baseShift S i)

/-- **The universal class of degree `i`**, `z₀ ∈ Hⁱ(S, Z₀)`: the class of the unit
`A[-i] ⟶ RΓ(S, L(A[-i]))` of `L ⊣ RΓ(S, -)`. -/
def cupUniversalClass (i : ℤ) :
    ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule (cupUniversalObject S i) i :=
  DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
    ((baseSections S).obj (cupUniversalObject S i)) i (baseRing S)
    ((onePointComparisonCanonical S).adjunction.unit.app (baseShift S i))

/-- The morphism representing the universal class is the unit of `L ⊣ RΓ(S, -)`. -/
theorem classRepresentative_cupUniversalClass (i : ℤ) :
    classRepresentative (cupUniversalObject S i) i (cupUniversalClass S i) =
      (onePointComparisonCanonical S).adjunction.unit.app (baseShift S i) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
    ((baseSections S).obj (cupUniversalObject S i)) i (baseRing S)).symm_apply_apply _

/-- The class `Hⁱ(g)(z₀)` of a morphism `g : Z₀ ⟶ Z` is the class attached to `g` by the inverse
of `classAdjunctEquiv`, Tag 06XS followed by the adjunction. -/
theorem cupUniversalClass_comp_eq (i : ℤ)
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (g : cupUniversalObject S i ⟶ Z) :
    cupUniversalClass S i ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
          ((baseSections S).map g) =
      (classAdjunctEquiv (onePointComparisonCanonical S) Z i).symm g := by
  change _ = DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
    ((baseSections S).obj Z) i (baseRing S)
      ((onePointComparisonCanonical S).adjunction.homEquiv _ _ g)
  rw [Adjunction.homEquiv_unit, DerivedCategory.homologyFromSingleLinearEquiv_comp]
  rfl

/-- **The universal property of the universal class.** For every `Z ∈ D(𝒪_S)`, a morphism
`g : Z₀ ⟶ Z` is determined by the class `Hⁱ(g)(z₀) ∈ Hⁱ(S, Z)`, and every class arises. -/
theorem bijective_cupUniversalClass_comp (i : ℤ)
    (Z : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    Function.Bijective (fun g : cupUniversalObject S i ⟶ Z ↦ cupUniversalClass S i ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
        ((baseSections S).map g)) := by
  rw [show (fun g : cupUniversalObject S i ⟶ Z ↦ cupUniversalClass S i ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) i).map
        ((baseSections S).map g)) = (classAdjunctEquiv (onePointComparisonCanonical S) Z i).symm
    from funext (cupUniversalClass_comp_eq S i Z)]
  exact Equiv.bijective _

/-- The global cup product `μ : RΓ(S, K) ⊗^𝐋_A RΓ(S, M) ⟶ RΓ(S, K ⊗^𝐋 M)` of Section 0FKU at a
pair, with its source and target written out. -/
abbrev canonicalCupMap (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    ((tensorBase S).obj ((baseSections S).obj K)).obj ((baseSections S).obj M) ⟶
      (baseSections S).obj (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S.sheaf).obj K).obj M) :=
  (globalCupProductCanonical S).app (K, M)

/-- The morphism `A[-i] ⊗^𝐋_A A[-j] ⟶ RΓ(S, Z₀ ⊗^𝐋 E)` attached to `s : A[-j] ⟶ RΓ(S, E)`:
the tensor product of `A[-i]` with `s`, the unit of `L ⊣ RΓ(S, -)` in the first factor, and the
global cup product. -/
def cupUniversalMap (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (s : baseShift S j ⟶ (baseSections S).obj E) :
    ((tensorBase S).obj (baseShift S i)).obj (baseShift S j) ⟶
      (baseSections S).obj (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        S.sheaf).obj (cupUniversalObject S i)).obj E) :=
  ((tensorBase S).obj (baseShift S i)).map s ≫
    ((tensorBase S).map ((onePointComparisonCanonical S).adjunction.unit.app
      (baseShift S i))).app ((baseSections S).obj E) ≫
    canonicalCupMap S (cupUniversalObject S i) E

/-- `cupUniversalMap`, with the unit moved past `s`. -/
theorem cupUniversalMap_eq (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)))
    (i j : ℤ) (s : baseShift S j ⟶ (baseSections S).obj E) :
    cupUniversalMap S E i j s =
      (((tensorBase S).map (classRepresentative _ i (cupUniversalClass S i))).app
          (baseShift S j) ≫
        ((tensorBase S).obj ((baseSections S).obj (cupUniversalObject S i))).map s) ≫
      canonicalCupMap S (cupUniversalObject S i) E := by
  rw [classRepresentative_cupUniversalClass, cupUniversalMap, Category.assoc,
    ← NatTrans.naturality_assoc]


/-- The cup product of the universal class with a class `η ∈ Hʲ(S, E)` is the class of
`pinnedSplitting` followed by `cupUniversalMap` of the morphism representing `η`. -/
theorem cupUniversalClass_cupPairing_eq
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule E j) :
    (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cupUniversalClass S i ⊗ₘ η) ≫
        cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i j =
      DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
        ((baseSections S).obj (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          S.sheaf).obj (cupUniversalObject S i)).obj E)) (i + j) (baseRing S)
        (pinnedSplitting S i j ≫ cupUniversalMap S E i j (classRepresentative E j η)) := by
  have h := homologyFromSingle_pinnedSplitting_comp (cupUniversalObject S i) E i j
    (cupUniversalClass S i) η
  have h₃ : pinnedSplitting S i j ≫ cupUniversalMap S E i j (classRepresentative E j η) =
      (pinnedSplitting S i j ≫
        (((tensorBase S).map (classRepresentative _ i (cupUniversalClass S i))).app
            (baseShift S j) ≫
          ((tensorBase S).obj ((baseSections S).obj (cupUniversalObject S i))).map
            (classRepresentative E j η))) ≫
        canonicalCupMap S (cupUniversalObject S i) E := by
    rw [cupUniversalMap_eq]
    simp only [Category.assoc]
  rw [h₃, DerivedCategory.homologyFromSingleLinearEquiv_comp]
  have h₅ := h =≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S)) (i + j)).map
    (canonicalCupMap S (cupUniversalObject S i) E)
  simp only [Category.assoc] at h₅
  exact h₅.symm

/-- `cupUniversalMap` is the abstract relative cup product of Tag 0B68 at `(L(A[-i]), E)`,
precomposed with the unit in the first factor. -/
theorem cupUniversalMap_eq_adjunctionBitensorMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (s : baseShift S j ⟶ (baseSections S).obj E) :
    cupUniversalMap S E i j s =
      (Functor.uncurry.obj (tensorBase S)).map (𝟙 (baseShift S i) ×ₘ s) ≫
        (Functor.uncurry.obj (tensorBase S)).map
          ((onePointComparisonCanonical S).adjunction.unit.app (baseShift S i) ×ₘ
            𝟙 ((baseSections S).obj E)) ≫
        Stacks.Cohomology.DerivedRelativeCupProduct.adjunctionBitensorMap
          (onePointComparisonCanonical S).adjunction (Functor.uncurry.obj (tensorBase S))
          (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf))
          (onePointComparisonCanonical S).tensorComparison (cupUniversalObject S i) E := by
  simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rfl

/-- **The cup product with the universal class is bijective**, as soon as `pinnedSplitting` is
invertible in bidegree `(i, j)` and tensoring on the left by `Z₀ = L(A[-i])` is fully faithful:
every class of `Hⁱ⁺ʲ(S, Z₀ ⊗^𝐋 E)` is `z₀ ∪ η` for exactly one `η ∈ Hʲ(S, E)`. -/
theorem bijective_cupUniversalClass_cupPairing
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ)
    (hps : IsIso (pinnedSplitting S i j))
    (hB : ∀ M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)),
      Function.Bijective (fun v : M ⟶ M' ↦
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.sheaf).obj
          (cupUniversalObject S i)).map v)) :
    Function.Bijective (fun η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule E j ↦
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cupUniversalClass S i ⊗ₘ η) ≫
        cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i j) := by
  have hfun : (fun η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule E j ↦
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cupUniversalClass S i ⊗ₘ η) ≫
        cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i j) =
      (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of (baseRing S) (baseRing S))
        ((baseSections S).obj (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
          S.sheaf).obj (cupUniversalObject S i)).obj E)) (i + j) (baseRing S)) ∘
        (fun w ↦ pinnedSplitting S i j ≫ w) ∘ (cupUniversalMap S E i j) ∘
        (classRepresentative E j) := by
    funext η
    exact cupUniversalClass_cupPairing_eq S E i j η
  rw [hfun]
  have hcup : Function.Bijective (cupUniversalMap S E i j) := by
    rw [funext (cupUniversalMap_eq_adjunctionBitensorMap S E i j)]
    refine Stacks.Cohomology.DerivedRelativeCupProduct.bijective_map_unit_comp_adjunctionBitensorMap
      _ _ _ _ _ _ _ inferInstance (fun M M' ↦ ?_)
    convert hB M M' using 2 with v
    exact Stacks.Cohomology.DerivedProjectionFormula.uncurry_map_id_left _ _ v
  refine (LinearEquiv.bijective _).comp (Function.Bijective.comp ?_
    (hcup.comp (LinearEquiv.bijective _)))
  exact (isIso_iff_coyoneda_map_bijective _).1 hps _

/-! ### The cup product with the universal class is bijective -/

/-- **The cup product with the universal class is bijective**: for every `E ∈ D(𝒪_S)` and all
degrees `i, j`, every class of `Hⁱ⁺ʲ(S, Z₀ ⊗^𝐋 E)` is `z₀ ∪ η` for exactly one
`η ∈ Hʲ(S, E)`, where `z₀ ∈ Hⁱ(S, Z₀)` is the universal class of degree `i` and the cup product is
the one of Section 0FKU at the canonical global cup product. -/
theorem bijective_cupUniversalClass_cupPairing_canonical
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) (i j : ℤ) :
    Function.Bijective (fun η : ModuleCat.of (baseRing S) (baseRing S) ⟶ cohomologyModule E j ↦
      (λ_ (ModuleCat.of (baseRing S) (baseRing S))).inv ≫ (cupUniversalClass S i ⊗ₘ η) ≫
        cupPairing (globalCupProductCanonical S) (cupUniversalObject S i) E i j) :=
  bijective_cupUniversalClass_cupPairing S E i j inferInstance
    (bijective_map_tensorPullbackBaseShift S i)

end Stacks.Cohomology.DerivedGlobalCupProduct

end
