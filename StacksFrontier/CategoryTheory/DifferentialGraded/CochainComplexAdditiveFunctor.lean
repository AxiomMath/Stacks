module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparison
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory

/-!
# Additive functors on the differential graded categories of complexes

An additive functor `F : B ⥤ B'` between preadditive categories acts componentwise on cochains,
and this makes it a functor of the differential graded categories of cochain complexes. The
ordinary functors it induces on closed degree-zero maps and on homotopy classes are the usual
functors on complexes and on their homotopy categories.

## Main definitions

* `CochainComplex.additiveFunctorDG`: the componentwise differential graded functor.

## Main results

* `CochainComplex.additiveFunctorDG_obj` and `CochainComplex.additiveFunctorDG_map`: its action
  on objects and on homogeneous morphisms.
* `CochainComplex.additiveFunctorDG_onComp` and `CochainComplex.additiveFunctorDG_onK`: the
  induced ordinary functors are the usual ones, through the canonical comparisons.

## Implementation notes

The canonical equivalences `CochainComplex.complexesCategoryEquivalence` and
`CochainComplex.homotopyCategoryEquivalence` compare closed degree-zero morphisms and homotopy
classes with the corresponding Mathlib categories, and the two functor equalities express
naturality of those comparisons in the additive functor.

## References

* [Stacks Project, Tag 09LB](https://stacks.math.columbia.edu/tag/09LB)
-/

public section

open CategoryTheory
open DGCategory
open CochainComplex.HomComplex

universe v₁ v₂ u₁ u₂

namespace CochainComplex

variable {B : Type u₁} {B' : Type u₂}
variable [Category.{v₁} B] [Preadditive B] [Category.{v₂} B'] [Preadditive B']
variable (F : B ⥤ B') [F.Additive]
include F

/-- Applying an additive functor to each component of a cochain defines a differential graded
functor on complexes. -/
@[local expose,
  stacks 09LB "the differential graded functor",
  sga "4 XVII 1.1.6" "one covariant variable"]
noncomputable def additiveFunctorDG (F : B ⥤ B') [F.Additive] :
    DGFunctor (dgCategory B) (dgCategory B') :=
  { obj := fun A => (F.mapHomologicalComplex (.up ℤ)).obj A
    map := fun f => f.map F
    map_add := fun f g => Cochain.map_add f g F
    map_smul := by
      intro A C n r f
      let φ : Cochain A C n →+ Cochain ((F.mapHomologicalComplex (.up ℤ)).obj A)
          ((F.mapHomologicalComplex (.up ℤ)).obj C) n :=
        { toFun := fun x => x.map F
          map_zero' := by simp
          map_add' := by intro x y; exact Cochain.map_add x y F }
      change φ (r • f) = r • φ f
      exact map_zsmul φ r f
    map_d := by
      intro A C n f
      change (δ n (n + 1) f).map F = δ n (n + 1) (f.map F)
      exact (δ_map n (n + 1) f F).symm
    map_comp := by
      intro A C D m n k h g f
      change (f.comp g (by lia)).map F =
        (f.map F).comp (g.map F) (by lia)
      ext p q hpq
      simp
    map_id := by
      intro A
      let A₀ : CochainComplex B ℤ := A
      let A₁ : CochainComplex B' ℤ := (F.mapHomologicalComplex (.up ℤ)).obj A₀
      change (Cochain.ofHom (𝟙 A₀)).map F = Cochain.ofHom (𝟙 A₁)
      rw [Cochain.map_ofHom]
      simp [A₀, A₁, (F.mapHomologicalComplex (.up ℤ)).map_id A₀] }

/-- The differential graded functor applies `F` degreewise to objects. -/
@[stacks 09LB "action on objects"]
theorem additiveFunctorDG_obj (A : CochainComplex B ℤ) :
    (additiveFunctorDG F).obj A = (F.mapHomologicalComplex (.up ℤ)).obj A :=
  rfl

/-- The differential graded functor applies `F` to every component of a homogeneous map. -/
@[stacks 09LB "action on homogeneous morphisms"]
theorem additiveFunctorDG_map {A C : CochainComplex B ℤ} {n : ℤ}
    (f : Cochain A C n) :
    HEq ((additiveFunctorDG F).map f) (f.map F) :=
  HEq.rfl

private theorem additiveFunctorDG_onComp_obj_eq
    (A : (dgCategory B).Comp) :
    (complexesCategoryEquivalence B').1.functor.obj
        ((additiveFunctorDG F).onComp.obj A) =
      (F.mapHomologicalComplex (.up ℤ)).obj
        ((complexesCategoryEquivalence B).1.functor.obj A) := by
  rw [(complexesCategoryEquivalence B').property.1,
    (complexesCategoryEquivalence B).property.1]
  rfl

/-- On closed degree-zero maps, the differential graded functor is the usual functor on
cochain complexes, through the canonical comparisons. -/
@[stacks 09LB "induced functor on complexes"]
theorem additiveFunctorDG_onComp :
    (additiveFunctorDG F).onComp ⋙ (complexesCategoryEquivalence B').1.functor =
      (complexesCategoryEquivalence B).1.functor ⋙ F.mapHomologicalComplex (.up ℤ) := by
  apply CategoryTheory.Functor.ext
    (fun A => additiveFunctorDG_onComp_obj_eq F A) (fun A C f => ?_)
  simp only [Functor.comp_map]
  apply HomologicalComplex.hom_ext
  intro i
  have hX' : ∀ A : (dgCategory B').Comp,
      ((complexesCategoryEquivalence B').1.functor.obj A).X i = A.X i := fun A =>
    congrArg (fun K : CochainComplex B' ℤ => K.X i) ((complexesCategoryEquivalence B').property.1 A)
  have hX : ∀ A : (dgCategory B).Comp,
      ((complexesCategoryEquivalence B).1.functor.obj A).X i = A.X i := fun A =>
    congrArg (fun K : CochainComplex B ℤ => K.X i) ((complexesCategoryEquivalence B).property.1 A)
  have hLA := hX' ((additiveFunctorDG F).onComp.obj A)
  have hLC := hX' ((additiveFunctorDG F).onComp.obj C)
  have hRA := hX A
  have hRC := hX C
  have hL := (complexesCategoryEquivalence B').property.2
    ((additiveFunctorDG F).onComp.obj A) ((additiveFunctorDG F).onComp.obj C)
    ((additiveFunctorDG F).onComp.map f) i
  have hR := (complexesCategoryEquivalence B).property.2 A C f i
  have hL' := (CategoryTheory.conj_eqToHom_iff_heq _ _ hLA hLC).2 hL
  have hR' := (CategoryTheory.conj_eqToHom_iff_heq _ _ hRA hRC).2 hR
  rw [hL']
  have hO : ∀ A : (dgCategory B).Comp,
      ((complexesCategoryEquivalence B').1.functor.obj ((additiveFunctorDG F).onComp.obj A)).X i =
        ((F.mapHomologicalComplex (.up ℤ)).obj
          ((complexesCategoryEquivalence B).1.functor.obj A)).X i := fun A =>
    congrArg (fun K : CochainComplex B' ℤ => K.X i) (additiveFunctorDG_onComp_obj_eq F A)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f]
  show eqToHom hLA ≫ F.map (f.1.v i i (add_zero i)) ≫ eqToHom hLC.symm =
    eqToHom (hO A) ≫ F.map (((complexesCategoryEquivalence B).1.functor.map f).f i) ≫
      eqToHom (hO C).symm
  rw [hR']
  have he : ∀ A, hO A = (hX' _).trans (congrArg F.obj (hX A).symm) := fun _ => Subsingleton.elim _ _
  rw [he A, he C]
  simp [Functor.map_comp, Category.assoc,
    CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_trans]
  rfl

/-- On homotopy classes, the differential graded functor is the usual functor on homotopy
categories, through the canonical comparisons. -/
@[stacks 09LB "induced functor on homotopy categories"]
theorem additiveFunctorDG_onK :
    letI : Category (dgCategory B).K :=
      (dgCategory B).instCategoryK
    letI : Category (dgCategory B').K :=
      (dgCategory B').instCategoryK
    F.mapHomotopyCategory (.up ℤ) ⋙ (homotopyCategoryEquivalence B').functor =
      (homotopyCategoryEquivalence B).functor ⋙ (additiveFunctorDG F).onK := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) (fun X Y f => ?_)
  rw [← HomotopyCategory.quotient_map_out f]
  let g := Quot.out f
  let cF : (dgCategory B').Cocycle _ _ :=
    ⟨Cochain.ofHom ((F.mapHomologicalComplex (.up ℤ)).map g), by
      show δ 0 1 (Cochain.ofHom ((F.mapHomologicalComplex (.up ℤ)).map g)) = 0
      exact δ_ofHom ((F.mapHomologicalComplex (.up ℤ)).map g)⟩
  let cG : (dgCategory B).Cocycle _ _ :=
    ⟨Cochain.ofHom g, by
      show δ 0 1 (Cochain.ofHom g) = 0
      exact δ_ofHom g⟩
  show HEq (Quotient.mk _ cF)
    (Quotient.mk _ ((additiveFunctorDG F).mapCocycle cG))
  apply heq_of_eq
  congr 1
  apply Subtype.ext
  simp [cF, cG, DGFunctor.mapCocycle, additiveFunctorDG, Cochain.map_ofHom]

end CochainComplex
