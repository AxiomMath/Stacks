module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct

/-!
# The augmentation square for the Čech cup product

Let `W : ι → C` be a family of objects of a category with finite products, let `R` be a
commutative ring, and let `D` be a pairing of complexes `K` and `L` of presheaves of
`R`-modules into a complex `M`, as in `Stacks.Cech.LinearCupProduct.ComplexPairing`.  Suppose
moreover that `C` has a terminal object `Z` -- for the Čech complex of a covering of an open
`V`, taken in the slice over `V`, the terminal object is `V` itself.

The pairing then has two cup products attached to it:

* the **naive** one, `Tot(K(Z) ⊗_R L(Z)) ⟶ M(Z)`, the totalization of the degreewise pairings
  evaluated at `Z`; and
* the **Čech** one of [Stacks, Tag 07MB],
  `Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ⟶ Tot(Č(W,M))`, which is
  `Stacks.Cech.LinearCupProduct.cechCupProduct`.

This file builds the first and proves that the **augmentation** of [Stacks, Tag 07M9] -- the map
`P(Z) ⟶ Č^0(W,P) ⊆ Tot(Č(W,P))` restricting a section over `Z` to the members of the family --
carries the first to the second.

## Main definitions

* `Stacks.Cech.LinearCupProduct.naiveCupProduct`: the naive cup product
  `Tot(K(V) ⊗_R L(V)) ⟶ M(V)` of a `ComplexPairing`, at any object of `C`.
* `Stacks.Cech.LinearCupProduct.cechAugmentationCochains`: the augmentation
  `P(Z) ⟶ Č^0(W,P)` into Čech degree zero.
* `Stacks.Cech.LinearCupProduct.cechAugmentationTotal`: the augmentation of [Stacks, Tag 07M9]
  as a morphism of complexes `K(Z) ⟶ Tot(Č(W,K))`.

## Main results

* `Stacks.Cech.LinearCupProduct.cechAugmentation_cechAlexanderWhitney`: in Čech degree zero the
  Alexander--Whitney product of two augmented cochains is the augmentation of their pairing.
* `Stacks.Cech.LinearCupProduct.naiveCupProduct_cechCupProduct`: **the augmentation square.**
  The square

  ```
  Tot(K(Z) ⊗_R L(Z)) ──────── naive cup product ────────→ M(Z)
          │                                                 │
     aug ⊗ aug                                             aug
          ↓                                                 ↓
  Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ── Čech cup product ──→ Tot(Č(W,M))
  ```

  commutes, as a square of morphisms of complexes of `R`-modules.

## Implementation notes

*Why a terminal object.*  The augmentation needs, for every tuple `t` of indices, a map
`inter W t ⟶ Z` along which to restrict, and the proof that the Čech differential annihilates
its image needs those maps to be compatible with the reindexings `interMap`.  Terminality gives
both at once and with no further data, and it is what holds in the application: the Čech complex
of [Stacks, Tag 0FKV] is taken on the slice category over the covered open, whose terminal
object is that open.  No covering hypothesis is needed anywhere below -- the square is an
identity between two morphisms of complexes, not a statement about cohomology.

*The signs.*  The Alexander--Whitney sign of
`Stacks.Cech.LinearCupProduct.cechCupProduct_ι` is `cupProductSign n p r` with `r` the Čech
degree of the front face and `p` the Čech degree of the target.  Both vanish on the image of the
augmentation, so the sign is `(-1)^0 = 1` and the square commutes on the nose rather than up to
a sign; this is `cechCupProductSummand_eq` at `r = s = 0`, where the sign it records is
`(a * 0).negOnePow`.

*The Čech degree crossings.*  The augmentation lands in the summand of Čech degree `0` and
coefficient degree `n`, whose total degree is spelled `((0 : ℕ) : ℤ) + n` by the total complex
and `n` by the complex of sections; the Alexander--Whitney map lands in Čech degree `0 + 0`.

## References

* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open Stacks.CategoryTheory.CechComplex
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap tensorModulesMap_comp)

universe u w uC vC uR

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

/-! ### The naive cup product of a pairing of complexes -/

section Naive

variable {C : Type uC} [Category.{vC} C] (R : Type uR) [CommRing R]

/-- **Sections at one object of `C`**, on complexes of presheaves of `R`-modules. -/
noncomputable abbrev sectionsAtFunctor (V : Cᵒᵖ) :
    CochainComplex (PresheafModules.{u} C R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  ((CategoryTheory.evaluation Cᵒᵖ (ModuleCat.{u} R)).obj V).mapHomologicalComplex (up ℤ)

/-- Tensoring on the left is `tensorModulesMap` with an identity on the right. -/
theorem tensorModules_map_app {M M' N : ModuleCat.{u} R} (f : M ⟶ M') :
    ((tensorModules R).map f).app N = tensorModulesMap R f (𝟙 N) :=
  rfl

/-- Tensoring on the right is `tensorModulesMap` with an identity on the left. -/
theorem tensorModules_obj_map {M N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    ((tensorModules R).obj M).map g = tensorModulesMap R (𝟙 M) g :=
  rfl

variable {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **The naive cup product in one total degree**: on the summand of bidegree `(a, b)` it is the
degreewise pairing `K^a ⊗_R L^b ⟶ M^{a+b}` evaluated at `V`. -/
noncomputable def naiveCupProductDegree (D : ComplexPairing.{u} R K L M) (V : Cᵒᵖ) (n : ℤ) :
    (HomologicalComplex.mapBifunctor ((sectionsAtFunctor R V).obj K)
        ((sectionsAtFunctor R V).obj L) (tensorModules R) (up ℤ)).X n ⟶
      ((sectionsAtFunctor R V).obj M).X n :=
  HomologicalComplex.mapBifunctorDesc fun a b hab => (D.μ a b n hab).app V

/-- On the summand of bidegree `(a, b)`, the naive cup product in total degree `n` is the
degreewise pairing `K^a ⊗_R L^b ⟶ M^n` evaluated at `V`. -/
@[reassoc]
theorem ι_naiveCupProductDegree (D : ComplexPairing.{u} R K L M) (V : Cᵒᵖ) (a b n : ℤ)
    (hab : a + b = n) :
    HomologicalComplex.ιMapBifunctor ((sectionsAtFunctor R V).obj K)
          ((sectionsAtFunctor R V).obj L) (tensorModules R) (up ℤ) a b n hab ≫
        naiveCupProductDegree R D V n =
      (D.μ a b n hab).app V :=
  HomologicalComplex.ι_mapBifunctorDesc _ a b hab

/-- **The naive cup product of a pairing of complexes**, `Tot(K(V) ⊗_R L(V)) ⟶ M(V)`. -/
noncomputable def naiveCupProduct (D : ComplexPairing.{u} R K L M) (V : Cᵒᵖ) :
    HomologicalComplex.mapBifunctor ((sectionsAtFunctor R V).obj K)
        ((sectionsAtFunctor R V).obj L) (tensorModules R) (up ℤ) ⟶
      (sectionsAtFunctor R V).obj M where
  f := naiveCupProductDegree R D V
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
    have hab' : a + b = n := hab
    have h := congrArg (fun φ : (((tensorPresheafModules.{u} R).obj (K.X a)).obj (L.X b)) ⟶
        M.X (n + 1) => φ.app V) (D.μ_d a b n hab')
    simp only [NatTrans.comp_app, NatTrans.app_add, NatTrans.app_zsmul, Units.smul_def,
      tensorPresheafModules_map_left_app, tensorPresheafModules_map_right_app] at h
    rw [← Category.assoc, ι_naiveCupProductDegree, ← Category.assoc, tensorModules_ι_d]
    simp only [Units.smul_def, Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
      ι_naiveCupProductDegree]
    exact h

/-- The component in degree `n` of the naive cup product is `naiveCupProductDegree`. -/
@[simp]
theorem naiveCupProduct_f (D : ComplexPairing.{u} R K L M) (V : Cᵒᵖ) (n : ℤ) :
    (naiveCupProduct R D V).f n = naiveCupProductDegree R D V n :=
  rfl

end Naive

/-! ### The augmentation of Stacks 07M9, generically -/

section Augmentation

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C]
  {ι : Type w} [UnivLE.{w, u}] (W : ι → C) (R : Type uR) [CommRing R]
  {Z : C} (hZ : IsTerminal Z)

/-- **The augmentation into Čech degree zero**: restrict a section over the terminal object to
each of the formal intersections selected by a one-element tuple of indices. -/
noncomputable def cechAugmentationCochains (P : PresheafModules.{u} C R) :
    P.obj (op Z) ⟶ cechCochains W R P 0 :=
  lift W P fun t => P.map (hZ.from (inter W t)).op

/-- The component of the augmentation at a one-element tuple `t` is the restriction from the
terminal object to `inter W t`. -/
@[reassoc (attr := simp)]
theorem cechAugmentationCochains_comp_π (P : PresheafModules.{u} C R) (t : Fin 1 → ι) :
    cechAugmentationCochains W R hZ P ≫ π W P 0 t = P.map (hZ.from (inter W t)).op :=
  lift_comp_π W P _ t

/-- The augmentation followed by any face restriction is the restriction from the terminal
object. -/
theorem cechAugmentationCochains_comp_cechFaceRestriction (P : PresheafModules.{u} C R) {q : ℕ}
    (θ : Fin (0 + 1) → Fin (q + 1)) (t : Fin (q + 1) → ι) :
    cechAugmentationCochains W R hZ P ≫ cechFaceRestriction W R P θ t =
      P.map (hZ.from (inter W t)).op := by
  dsimp only [cechFaceRestriction]
  rw [← Category.assoc, cechAugmentationCochains_comp_π, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun g : inter W t ⟶ Z => P.map g.op) (hZ.hom_ext _ _)

/-- **The Čech differential annihilates the image of the augmentation.** -/
theorem cechAugmentationCochains_comp_cechD (P : PresheafModules.{u} C R) :
    cechAugmentationCochains W R hZ P ≫ cechD W R P 0 = 0 := by
  refine hom_ext W P fun y => ?_
  rw [Category.assoc, cechD_comp_π, zero_comp, Preadditive.comp_sum, Fin.sum_univ_two,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    cechAugmentationCochains_comp_cechFaceRestriction,
    cechAugmentationCochains_comp_cechFaceRestriction]
  simp

/-- **The augmentation is natural in the coefficient presheaf.** -/
@[reassoc]
theorem cechAugmentationCochains_naturality {P Q : PresheafModules.{u} C R} (f : P ⟶ Q) :
    cechAugmentationCochains W R hZ P ≫ cechCochainsMap W R f 0 =
      f.app (op Z) ≫ cechAugmentationCochains W R hZ Q := by
  refine hom_ext W Q fun t => ?_
  rw [Category.assoc, cechCochainsMap_comp_π, ← Category.assoc,
    cechAugmentationCochains_comp_π, Category.assoc, cechAugmentationCochains_comp_π]
  exact f.naturality (hZ.from (inter W t)).op

/-- **The augmentation of [Stacks, Tag 07M9] in one degree**: restrict into Čech degree zero and
include that summand of the total complex. -/
noncomputable def cechAugmentationDegree (K : CochainComplex (PresheafModules.{u} C R) ℤ)
    (n : ℤ) :
    ((sectionsAtFunctor R (op Z)).obj K).X n ⟶ ((totalCechComplexFunctor W R).obj K).X n :=
  cechAugmentationCochains W R hZ (K.X n) ≫ ιTotalCechTo W R K 0 n n (by push_cast; ring)

/-- **Stacks 07M9, generically.**  The augmentation `K(Z) ⟶ Tot(Č(W,K))`: in degree `n` restrict
into Čech degree zero and include that summand of the total complex. -/
noncomputable def cechAugmentationTotal (K : CochainComplex (PresheafModules.{u} C R) ℤ) :
    (sectionsAtFunctor R (op Z)).obj K ⟶ (totalCechComplexFunctor W R).obj K where
  f := cechAugmentationDegree W R hZ K
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    dsimp only [cechAugmentationDegree]
    rw [Category.assoc, ιTotalCechTo_d]
    simp only [Units.smul_def, Nat.cast_zero, Int.negOnePow_zero, Units.val_one, one_zsmul,
      Preadditive.comp_add, ← Category.assoc, cechAugmentationCochains_comp_cechD, zero_comp,
      zero_add, cechAugmentationCochains_naturality]
    rfl

/-- The component in degree `n` of the augmentation `K(Z) ⟶ Tot(Č(W,K))` is
`cechAugmentationDegree`. -/
@[simp]
theorem cechAugmentationTotal_f (K : CochainComplex (PresheafModules.{u} C R) ℤ) (n : ℤ) :
    (cechAugmentationTotal W R hZ K).f n = cechAugmentationDegree W R hZ K n :=
  rfl

/-! ### The augmentation square -/

/-- **The Alexander--Whitney product of two augmented cochains is the augmentation of their
pairing.** -/
theorem cechAugmentation_cechAlexanderWhitney {P Q T : PresheafModules.{u} C R}
    (μ : Pairing.{u} R P Q T) :
    tensorModulesMap R (cechAugmentationCochains W R hZ P)
          (cechAugmentationCochains W R hZ Q) ≫
        cechAlexanderWhitney W R μ 0 0 =
      μ.app (op Z) ≫ cechAugmentationCochains W R hZ T := by
  refine hom_ext W T fun t => ?_
  rw [Category.assoc, cechAlexanderWhitney_comp_π, Category.assoc,
    cechAugmentationCochains_comp_π]
  dsimp only [awTerm]
  rw [← Category.assoc, tensorModulesMap_comp,
    cechAugmentationCochains_comp_cechFaceRestriction,
    cechAugmentationCochains_comp_cechFaceRestriction]
  exact μ.naturality (hZ.from (inter W t)).op

variable {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **The tensor product of two augmentations, on a homogeneous summand.** On the summand of
bidegree `(a, b)` it is the tensor product of the two augmentations into Čech degree zero, followed
by the inclusion `ιTensorSource` of the summand of Čech bidegree `(0, 0)`. -/
theorem ι_mapBifunctorMap_cechAugmentationTotal (a b n : ℤ) (hab : a + b = n) :
    HomologicalComplex.ιMapBifunctor ((sectionsAtFunctor R (op Z)).obj K)
          ((sectionsAtFunctor R (op Z)).obj L) (tensorModules R) (up ℤ) a b n hab ≫
        (HomologicalComplex.mapBifunctorMap (cechAugmentationTotal W R hZ K)
          (cechAugmentationTotal W R hZ L) (tensorModules R) (up ℤ)).f n =
      tensorModulesMap R (cechAugmentationCochains W R hZ (K.X a))
          (cechAugmentationCochains W R hZ (L.X b)) ≫
        ιTensorSource W R K L 0 0 a b n (by push_cast; omega) := by
  rw [HomologicalComplex.ι_mapBifunctorMap, tensorModules_map_app, tensorModules_obj_map,
    ← Category.assoc, tensorModulesMap_comp, Category.comp_id, Category.id_comp,
    cechAugmentationTotal_f, cechAugmentationTotal_f]
  dsimp only [cechAugmentationDegree]
  rw [← tensorModulesMap_comp, Category.assoc,
    ιTensorSource_eq W R K L 0 0 a b a b n (by push_cast; ring) (by push_cast; ring) hab]

/-- **The target of the Čech cup product on the summand of Čech bidegree `(0, 0)`.** On two
augmented cochains it is the augmentation of their pairing, included in the total Čech complex. -/
theorem cechAugmentation_ιPairingTarget (D : ComplexPairing.{u} R K L M) (a b n : ℤ)
    (h : ((0 : ℕ) : ℤ) + a + (((0 : ℕ) : ℤ) + b) = n) :
    tensorModulesMap R (cechAugmentationCochains W R hZ (K.X a))
          (cechAugmentationCochains W R hZ (L.X b)) ≫
        ιPairingTarget W R D 0 0 a b n h =
      (D.μ a b (a + b) rfl).app (op Z) ≫
        cechAugmentationCochains W R hZ (M.X (a + b)) ≫
          ιTotalCechTo W R M 0 (a + b) n (by push_cast; omega) := by
  dsimp only [ιPairingTarget]
  rw [← Category.assoc, cechAugmentation_cechAlexanderWhitney, Category.assoc]

/-- The augmentation square, on one homogeneous summand of the source. -/
private theorem naiveCupProduct_cechCupProduct_summand (D : ComplexPairing.{u} R K L M)
    (a b n : ℤ) (hab : a + b = n) :
    HomologicalComplex.ιMapBifunctor ((sectionsAtFunctor R (op Z)).obj K)
          ((sectionsAtFunctor R (op Z)).obj L) (tensorModules R) (up ℤ) a b n hab ≫
        (HomologicalComplex.mapBifunctorMap (cechAugmentationTotal W R hZ K)
            (cechAugmentationTotal W R hZ L) (tensorModules R) (up ℤ) ≫
          cechCupProduct W R D).f n =
      HomologicalComplex.ιMapBifunctor ((sectionsAtFunctor R (op Z)).obj K)
          ((sectionsAtFunctor R (op Z)).obj L) (tensorModules R) (up ℤ) a b n hab ≫
        (naiveCupProduct R D (op Z) ≫ cechAugmentationTotal W R hZ M).f n := by
  subst hab
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    ι_mapBifunctorMap_cechAugmentationTotal, Category.assoc]
  show _ ≫ ιTensorSource W R K L 0 0 a b (a + b) _ ≫ cechCupProductDegree W R D (a + b) = _
  rw [ιTensorSource_cechCupProductDegree, cechCupProductSummand_eq]
  simp only [Nat.cast_zero, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul]
  rw [cechAugmentation_ιPairingTarget, naiveCupProduct_f,
    ι_naiveCupProductDegree_assoc, cechAugmentationTotal_f]
  rfl

/-- **The augmentation square of [Stacks, Tag 0FKV].**  The Čech cup product of [Stacks, Tag
07MB] applied to two augmented sections is the augmentation of their naive cup product:

```
Tot(K(Z) ⊗_R L(Z)) ──────── naive cup product ────────→ M(Z)
        │                                                 │
   aug ⊗ aug                                             aug
        ↓                                                 ↓
Tot(Tot(Č(W,K)) ⊗_R Tot(Č(W,L))) ── Čech cup product ──→ Tot(Č(W,M))
```

commutes.  This is an identity of morphisms of complexes of `R`-modules; no covering hypothesis
and no boundedness enters. -/
theorem naiveCupProduct_cechCupProduct (D : ComplexPairing.{u} R K L M) :
    HomologicalComplex.mapBifunctorMap (cechAugmentationTotal W R hZ K)
          (cechAugmentationTotal W R hZ L) (tensorModules R) (up ℤ) ≫
        cechCupProduct W R D =
      naiveCupProduct R D (op Z) ≫ cechAugmentationTotal W R hZ M := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine HomologicalComplex.mapBifunctor.hom_ext fun a b hab => ?_
  exact naiveCupProduct_cechCupProduct_summand W R hZ D a b n hab

end Augmentation

end Stacks.Cech.LinearCupProduct

end
