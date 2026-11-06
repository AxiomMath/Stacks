module

public import Mathlib.Algebra.Homology.Single
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The augmentation of a Čech-style complex at a terminal object

Let `C` be a category with a terminal object `T`, let `E` be a simplicial object of the category
`CategoryTheory.Limits.FormalCoproduct C` of formal coproducts of objects of `C`, and let `A` be a
preadditive category with products.  `Mathlib`'s
`CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor E` sends a presheaf `P : Cᵒᵖ ⥤ A` to
the cochain complex whose degree `n` term is the product `∏_{i ∈ Eₙ.I} P(Eₙ(i))` and whose
differential is the alternating sum of the coface maps of `E`.

This file constructs the canonical augmentation of that complex:  the map

`P(T) ⟶ ∏_{i ∈ E₀.I} P(E₀(i))`

whose `i`-th component is the restriction along the unique morphism `E₀(i) ⟶ T`.  It is a cycle in
degree zero, because the two coface maps `E₁ ⟶ E₀` become equal after composing with the unique
morphism to `T`, so the two summands of the first differential cancel.  It is therefore a morphism
of complexes out of `P(T)` placed in degree zero, natural in `P`.

Nothing here is specific to a site:  the three defining conditions of a hypercovering play no role
and no topology is mentioned.  The augmentation is the degree-zero half of the data `(T, ε)` of
[Stacks, Tag 09VX], and a simplicial object of formal coproducts is the shape of a hypercovering of
the terminal object, but the statements below hold for an arbitrary simplicial object of formal
coproducts, so no `@[stacks]` attribute is placed.

## Main definitions

* `Stacks.CategoryTheory.FormalCoproductAugmentation.cofaceMap`:  the `i`-th coface map of the
  cosimplicial object obtained by evaluating a presheaf on `E`, written in the product spelling.
* `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAug`:  the canonical map from the
  sections of `P` over `T` to the degree `n` product.
* `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAugZero`:  the same map in degree
  zero, with its target written as the degree-zero term of the complex.
* `Stacks.CategoryTheory.FormalCoproductAugmentation.terminalAugNatTrans`:  the augmentation as a
  natural transformation from the sections over `T`, placed in degree zero, to the complex.

## Main results

* `cochainComplexObj_X_eq`, `cochainComplexObj_d_eq`, `cochainComplexMap_f_eq`:  the degree `n`
  term of the complex, its differential as the alternating sum of the coface maps, and the degree
  `n` component of the map induced by a morphism of presheaves.
* `terminalAug_comp_cofaceMap`:  composing the augmentation with any coface map gives the
  augmentation one degree up; this is where the terminality of `T` enters.
* `terminalAugZero_comp_d`:  the augmentation is a cycle in degree zero.
* `terminalAug_naturality`:  the augmentation is natural in the presheaf.

## Implementation notes

Every statement whose objects are the degreewise products is written in the *product* spelling
`∏ᶜ fun i ↦ P.obj (op (Eₙ.obj i))` and not as `((cochainComplexFunctor E).obj P).X n`, even though
the two are definitionally equal.  This is the discipline recorded in
`StacksFrontier.CategoryTheory.Limits.FormalCoproductLinear`:  a goal mixing the two spellings is no
longer type-correct at `implicit` transparency, and `rw` then fails on patterns it is visibly
printing.  The passage between the spellings happens only in `terminalAugZero`,
`cochainComplexObj_d_eq` and `cochainComplexMap_f_eq`, each of which is discharged by a single
`exact` or `show` rather than by a rewrite.

## References

* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
-/

@[expose] public section

universe w v' u' v u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

namespace Stacks.CategoryTheory.FormalCoproductAugmentation

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [Preadditive A]
  (E : SimplicialObject (FormalCoproduct.{w} C))

/-! ### The coface maps in the product spelling -/

/-- **The `i`-th coface map of the cosimplicial object** obtained by evaluating a presheaf on `E`:
on the factor indexed by `j`, it is the restriction map of `P` along the `j`-th component of the
`i`-th face map of `E`, read out of the factor indexed by the image of `j`. -/
noncomputable def cofaceMap (P : Cᵒᵖ ⥤ A) (n : ℕ) (i : Fin (n + 2)) :
    ∏ᶜ (fun k : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj k))) ⟶
      ∏ᶜ (fun j : (E.obj (op ⦋n + 1⦌)).I ↦ P.obj (op ((E.obj (op ⦋n + 1⦌)).obj j))) :=
  Limits.Pi.lift (fun j : (E.obj (op ⦋n + 1⦌)).I ↦
    Limits.Pi.π (fun k : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj k)))
        ((E.map (SimplexCategory.δ i).op).f j) ≫
      P.map ((E.map (SimplexCategory.δ i).op).φ j).op)

omit [Preadditive A] in
/-- The component of `cofaceMap E P n i` on the factor indexed by `j` is the projection onto the
factor indexed by the image of `j` under the `i`-th face map, followed by the restriction map of
`P` along the `j`-th component of that face map. -/
@[reassoc]
theorem cofaceMap_comp_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (i : Fin (n + 2)) (j : (E.obj (op ⦋n + 1⦌)).I) :
    cofaceMap E P n i ≫
        Limits.Pi.π
          (fun l : (E.obj (op ⦋n + 1⦌)).I ↦ P.obj (op ((E.obj (op ⦋n + 1⦌)).obj l))) j =
      Limits.Pi.π (fun k : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj k)))
          ((E.map (SimplexCategory.δ i).op).f j) ≫
        P.map ((E.map (SimplexCategory.δ i).op).φ j).op :=
  Limits.Pi.lift_comp_π _ _

/-! ### The shape of the Čech-style complex -/

/-- **The degree `n` term of the Čech-style complex** of a simplicial object of formal coproducts
is the product, over the index type of `Eₙ`, of the values of the presheaf on the components
of `Eₙ`. -/
theorem cochainComplexObj_X_eq (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor E).obj P).X n =
      ∏ᶜ (fun i : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj i))) :=
  rfl

/-- **The differential of the Čech-style complex is the alternating sum of the coface maps.** -/
theorem cochainComplexObj_d_eq (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor E).obj P).d n (n + 1) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • cofaceMap E P n i := by
  show ((alternatingCofaceMapComplex A).obj
    ((FormalCoproduct.cosimplicialObjectFunctor E).obj P)).d n (n + 1) = _
  exact CochainComplex.of_d _
    (AlternatingCofaceMapComplex.objD ((FormalCoproduct.cosimplicialObjectFunctor E).obj P)) n

/-- **The degree `n` component of the map of complexes induced by a morphism of presheaves** is
the product of its components. -/
theorem cochainComplexMap_f_eq {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    ((FormalCoproduct.cochainComplexFunctor E).map α).f n =
      Limits.Pi.map (fun i : (E.obj (op ⦋n⦌)).I ↦ α.app (op ((E.obj (op ⦋n⦌)).obj i))) :=
  rfl

/-! ### The augmentation -/

variable {T : C} (hT : IsTerminal T)

/-- **The canonical augmentation of the Čech-style complex in degree `n`.**  Its component on the
factor indexed by `i` is the restriction map of `P` along the unique morphism `Eₙ(i) ⟶ T`. -/
noncomputable def terminalAug (P : Cᵒᵖ ⥤ A) (n : ℕ) :
    P.obj (op T) ⟶ ∏ᶜ (fun i : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj i))) :=
  Limits.Pi.lift (fun i : (E.obj (op ⦋n⦌)).I ↦ P.map (hT.from ((E.obj (op ⦋n⦌)).obj i)).op)

omit [Preadditive A] in
/-- The component of `terminalAug E hT P n` on the factor indexed by `i` is the restriction map
of `P` along the unique morphism `Eₙ(i) ⟶ T`. -/
@[reassoc]
theorem terminalAug_comp_π (P : Cᵒᵖ ⥤ A) (n : ℕ) (i : (E.obj (op ⦋n⦌)).I) :
    terminalAug E hT P n ≫
        Limits.Pi.π (fun k : (E.obj (op ⦋n⦌)).I ↦ P.obj (op ((E.obj (op ⦋n⦌)).obj k))) i =
      P.map (hT.from ((E.obj (op ⦋n⦌)).obj i)).op :=
  Limits.Pi.lift_comp_π _ _

omit [Preadditive A] in
/-- **Composing the augmentation with a coface map gives the augmentation one degree up.**  This
is the only place terminality is used:  the `j`-th component of the face map, followed by the
unique morphism to `T`, is again the unique morphism to `T`. -/
theorem terminalAug_comp_cofaceMap (P : Cᵒᵖ ⥤ A) (n : ℕ) (i : Fin (n + 2)) :
    terminalAug E hT P n ≫ cofaceMap E P n i = terminalAug E hT P (n + 1) := by
  refine Limits.Pi.hom_ext _ _ (fun j ↦ ?_)
  rw [Category.assoc, cofaceMap_comp_π, terminalAug_comp_π_assoc, ← P.map_comp, ← op_comp,
    terminalAug_comp_π,
    hT.hom_ext ((E.map (SimplexCategory.δ i).op).φ j ≫
      hT.from ((E.obj (op ⦋n⦌)).obj ((E.map (SimplexCategory.δ i).op).f j)))
      (hT.from ((E.obj (op ⦋n + 1⦌)).obj j))]

/-- **The augmentation is a cycle in degree zero**, in the product spelling:  the first
differential is the difference of the two coface maps out of degree zero, and the augmentation
composed with either of them is the augmentation in degree one. -/
theorem terminalAug_comp_alternatingSum (P : Cᵒᵖ ⥤ A) :
    terminalAug E hT P 0 ≫ (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • cofaceMap E P 0 i) = 0 := by
  rw [Preadditive.comp_sum, Fin.sum_univ_two, Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    terminalAug_comp_cofaceMap, terminalAug_comp_cofaceMap]
  simp

/-- **The canonical augmentation in degree zero**, with its target written as the degree-zero term
of the complex. -/
noncomputable def terminalAugZero (P : Cᵒᵖ ⥤ A) :
    P.obj (op T) ⟶ ((FormalCoproduct.cochainComplexFunctor E).obj P).X 0 :=
  terminalAug E hT P 0

/-- **The augmentation is a cycle in degree zero.** -/
theorem terminalAugZero_comp_d (P : Cᵒᵖ ⥤ A) :
    terminalAugZero E hT P ≫ ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 1 = 0 := by
  have hd : ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 1 =
      ∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • cofaceMap E P 0 i :=
    cochainComplexObj_d_eq E P 0
  exact hd ▸ terminalAug_comp_alternatingSum E hT P

/-- The augmentation is a cycle in degree zero, in the form the constructor for morphisms out of
a complex concentrated in degree zero asks for. -/
theorem terminalAugZero_comp_d_rel (P : Cᵒᵖ ⥤ A) (k : ℕ) (hk : (ComplexShape.up ℕ).Rel 0 k) :
    terminalAugZero E hT P ≫ ((FormalCoproduct.cochainComplexFunctor E).obj P).d 0 k = 0 := by
  obtain rfl : k = 1 := by simpa using hk.symm
  exact terminalAugZero_comp_d E hT P

omit [Preadditive A] in
/-- **The augmentation is natural in the presheaf.** -/
theorem terminalAug_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) (n : ℕ) :
    α.app (op T) ≫ terminalAug E hT Q n =
      terminalAug E hT P n ≫
        Limits.Pi.map (fun i : (E.obj (op ⦋n⦌)).I ↦ α.app (op ((E.obj (op ⦋n⦌)).obj i))) := by
  refine Limits.Pi.hom_ext _ _ (fun j ↦ ?_)
  rw [Category.assoc, terminalAug_comp_π, Category.assoc, Limits.Pi.map_π,
    terminalAug_comp_π_assoc]
  exact (α.naturality (hT.from ((E.obj (op ⦋n⦌)).obj j)).op).symm

/-- `terminalAug_naturality` in degree zero, with the objects written as the terms of the
complex. -/
theorem terminalAugZero_naturality {P Q : Cᵒᵖ ⥤ A} (α : P ⟶ Q) :
    α.app (op T) ≫ terminalAugZero E hT Q =
      terminalAugZero E hT P ≫ ((FormalCoproduct.cochainComplexFunctor E).map α).f 0 := by
  have h := cochainComplexMap_f_eq E α 0
  exact h ▸ terminalAug_naturality E hT α 0

/-! ### The augmentation as a morphism of complexes -/

variable [HasZeroObject A]

/-- **The augmentation of the Čech-style complex**, as a natural transformation from the sections
over the terminal object, placed in degree zero, to the complex itself. -/
noncomputable def terminalAugNatTrans :
    (evaluation Cᵒᵖ A).obj (op T) ⋙ HomologicalComplex.single A (ComplexShape.up ℕ) 0 ⟶
      FormalCoproduct.cochainComplexFunctor E where
  app P := HomologicalComplex.mkHomFromSingle (terminalAugZero E hT P)
    (terminalAugZero_comp_d_rel E hT P)
  naturality P Q α := by
    refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
    simp only [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
      Functor.comp_map, HomologicalComplex.single_map_f_self, evaluation_obj_map,
      Category.assoc, Iso.inv_hom_id_assoc]
    exact congrArg
      (fun z ↦ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 (P.obj (op T))).hom ≫ z)
      (terminalAugZero_naturality E hT α)

/-- The degree-zero component of `terminalAugNatTrans` is `terminalAugZero`. -/
theorem terminalAugNatTrans_f_zero (P : Cᵒᵖ ⥤ A) :
    ((terminalAugNatTrans E hT).app P).f 0 = terminalAugZero E hT P :=
  (HomologicalComplex.mkHomFromSingle_f (terminalAugZero E hT P)
    (terminalAugZero_comp_d_rel E hT P)).trans (Category.id_comp _)

end Stacks.CategoryTheory.FormalCoproductAugmentation

end
