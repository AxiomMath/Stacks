module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.NerveFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverBased
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.FibrewiseEquivalence

/-!
# The terms of the relative Čech nerve as categories over the base

Let `p : X ⥤ C` be a category over `C` and `f : U ⥤ X` a functor. The degree `n` term `Uₙ` of the
relative Čech nerve of `f` (`Stacks.RelativeCech.Tuple`) is a category over `C` through its
projection to `X`. This file shows that, *over `C`*,

* `U₀` is equivalent to `U` with the structure functor `f ⋙ p`, and
* `U_{n + 1}` is equivalent to the 2-fibre product `U ×_X Uₙ` with its structure functor,

in the sense of `CategoryTheory.StacksRepresentableCFG.EquivalenceOver`: strictly commuting
1-morphisms with vertical unit and counit. The underlying equivalences of categories are
`Stacks.RelativeCech.isEquivalence_coordinate_zero` and
`Stacks.RelativeCech.isEquivalence_fibreProductToNerve`.

## Main definitions

* `Stacks.RelativeCech.tupleSuccToNerveFibreProduct`: `U_{n + 1} ⥤ U ×_X Uₙ` into the
  2-fibre product `Stacks.RelativeCech.nerveFibreProduct`, splitting off the first coordinate; it
  is strictly over `C`.
* `Stacks.RelativeCech.tupleZeroEquivalenceOver`, `Stacks.RelativeCech.tupleSuccEquivalenceOver`:
  the two equivalences over `C`.

## References

* [Stacks Project, Tag 06X3](https://stacks.math.columbia.edu/tag/06X3)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.RelativeCech

universe vC vU vX uC uU uX

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] (p : X ⥤ C) (f : U ⥤ X)

/-- An entry of a Čech tuple lies over the base object of its target. -/
theorem Tuple.obj_source_eq {n : ℕ} (A : Tuple p f n) (i : Fin (n + 1)) :
    p.obj (f.obj (A.source i)) = p.obj A.target :=
  have := A.comparison_lift i
  IsHomLift.domain_eq p (𝟙 (p.obj A.target)) (A.comparison i).hom

/-- The comparison isomorphism of a Čech tuple entry lies over the identity of the base. -/
private theorem Tuple.map_comparison_hom_eq {n : ℕ} (A : Tuple p f n) (i : Fin (n + 1)) :
    p.map (A.comparison i).hom = eqToHom (Tuple.obj_source_eq p f A i) := by
  have := A.comparison_lift i
  simpa using IsHomLift.fac' p (𝟙 (p.obj A.target)) (A.comparison i).hom

/-- An entry of a morphism of Čech tuples lies over the image of its target morphism. -/
theorem Tuple.map_source_eq {n : ℕ} {A B : Tuple p f n} (φ : A ⟶ B) (i : Fin (n + 1)) :
    p.map (f.map (Tuple.Hom.source φ i)) =
      eqToHom (Tuple.obj_source_eq p f A i) ≫ p.map (Tuple.Hom.target φ) ≫
        eqToHom (Tuple.obj_source_eq p f B i).symm := by
  have h := congrArg p.map (Tuple.Hom.comparison_naturality φ i)
  rw [p.map_comp, p.map_comp, Tuple.map_comparison_hom_eq, Tuple.map_comparison_hom_eq] at h
  rw [← cancel_mono (eqToHom (Tuple.obj_source_eq p f B i)), h]
  simp

/-- The first coordinate of a one-entry tuple lies over the base of the tuple: reading off the
coordinate is a 1-morphism over `C` from `U₀`, with its structure functor `Tp 0 ⋙ p`, to `U`,
with `f ⋙ p`. -/
theorem coordinate_zero_comp_eq :
    Tuple.coordinate p f (0 : Fin 1) ⋙ f ⋙ p = Tuple.projection p f 0 ⋙ p :=
  CategoryTheory.Functor.ext (fun (A : Tuple p f 0) => Tuple.obj_source_eq p f A 0)
    (fun (A B : Tuple p f 0) (φ : A ⟶ B) => Tuple.map_source_eq p f φ 0)

/-- The one-entry tuple on the first coordinate of a one-entry tuple is isomorphic to it, by
the comparison isomorphism of that coordinate. -/
def toTupleZeroCoordinateIso (A : Tuple p f 0) :
    (toTupleZero p f).obj (A.source 0) ≅ A :=
  Stacks.Cech.tupleIso (A.comparison 0)
    (fun i => Fin.cases (motive := fun i => A.source 0 ≅ A.source i) (Iso.refl _)
      (fun j => j.elim0) i)
    (fun i => by
      cases i using Fin.cases with
      | zero =>
        change f.map (𝟙 (A.source 0)) ≫ (A.comparison 0).hom = 𝟙 _ ≫ (A.comparison 0).hom
        simp
      | succ j => exact j.elim0)

/-- **The degree zero term of the Čech nerve of `f : U ⥤ X` is `U`, over `C`.** The functor
`U ⥤ U₀` of one-entry tuples is an equivalence over `C`, with quasi-inverse the first
coordinate and unit and counit vertical. -/
def toTupleZeroIsEquivalenceOver :
    Functor.IsEquivalenceOver (f ⋙ p) (Tuple.projection p f 0 ⋙ p) (toTupleZero p f) where
  inv := Tuple.coordinate p f (0 : Fin 1)
  inv_over := coordinate_zero_comp_eq p f
  unitIso := NatIso.ofComponents (fun x => Iso.refl x)
    (fun g => (Category.comp_id _).trans (Category.id_comp _).symm)
  counitIso := NatIso.ofComponents (toTupleZeroCoordinateIso p f) (fun {A B} φ => by
    refine Stacks.Cech.tupleHom_ext ?_ (funext fun i => ?_)
    · exact Tuple.Hom.comparison_naturality φ 0
    · cases i using Fin.cases with
      | zero => exact (Category.comp_id _).trans (Category.id_comp _).symm
      | succ j => exact j.elim0)
  unit_vertical := fun x => by
    change (f ⋙ p).IsHomLift (𝟙 ((f ⋙ p).obj x)) (𝟙 x)
    infer_instance
  counit_vertical := fun A => by
    have := A.comparison_lift 0
    refine IsHomLift.of_fac' _ _ _ rfl (Tuple.obj_source_eq p f A 0).symm ?_
    change p.map (A.comparison 0).hom = _
    rw [IsHomLift.fac' p (𝟙 (p.obj A.target)) (A.comparison 0).hom]
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- The degree zero term of the Čech nerve of `f : U ⥤ X`, with its structure functor to `C`,
is equivalent over `C` to `U` with the structure functor `f ⋙ p`. -/
def tupleZeroEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (f ⋙ p) (Tuple.projection p f 0 ⋙ p) :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver rfl
    (toTupleZeroIsEquivalenceOver p f)

/-- The functor `U_{n + 1} ⥤ U ×_X U_n` splitting off the first coordinate of a tuple: the
first coordinate is the object of `U`, the remaining ones form the tuple of length `n + 1`, and
the first comparison isomorphism is the comparison of the 2-fibre product. It lies strictly over
`C`: the base object is the one below the target of the tuple. -/
def tupleSuccToNerveFibreProduct (n : ℕ) : Tuple p f (n + 1) ⥤ nerveFibreProduct p f n where
  obj A :=
    { base := p.obj A.target
      x := A.source 0
      y := { target := A.target
             source := fun i => A.source i.succ
             comparison := fun i => A.comparison i.succ
             comparison_lift := fun i => A.comparison_lift i.succ }
      hx := Tuple.obj_source_eq p f A 0
      hy := rfl
      iso := A.comparison 0
      vertical := A.comparison_lift 0 }
  map {A B} φ :=
    { hbase := p.map (Tuple.Hom.target (a := A) (b := B) φ)
      a := Tuple.Hom.source (a := A) (b := B) φ 0
      b := { target := Tuple.Hom.target (a := A) (b := B) φ
             source := fun i => Tuple.Hom.source (a := A) (b := B) φ i.succ
             comparison_naturality := fun i =>
               Tuple.Hom.comparison_naturality (a := A) (b := B) φ i.succ }
      ha := IsHomLift.of_fac' _ _ _ (Tuple.obj_source_eq p f A 0) (Tuple.obj_source_eq p f B 0)
        (Tuple.map_source_eq p f φ 0)
      hb := IsHomLift.of_fac' _ _ _ rfl rfl (by
        rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl)
      w := Tuple.Hom.comparison_naturality φ 0 }
  map_id A := by
    apply TwoFibreProductOver.Hom.ext'
    · rfl
    · exact Stacks.Cech.tupleHom_ext rfl rfl
  map_comp φ ψ := by
    apply TwoFibreProductOver.Hom.ext'
    · rfl
    · exact Stacks.Cech.tupleHom_ext rfl rfl

/-- Prepending a coordinate is a 1-morphism over `C`, from the 2-fibre product `U ×_X U_n` with
its structure functor to `U_{n + 1}` with the structure functor `Tp (n + 1) ⋙ p`. -/
theorem fibreProductToNerve_comp_eq (n : ℕ) :
    fibreProductToNerve p f n ⋙ Tuple.projection p f (n + 1) ⋙ p =
      TwoFibreProductOver.structureFunctor (f ⋙ p) (Tuple.projection p f n ⋙ p) p f
        (Tuple.projection p f n) :=
  CategoryTheory.Functor.ext (fun (P : nerveFibreProduct p f n) => P.hy)
    (fun (P Q : nerveFibreProduct p f n) (k : P ⟶ Q) => by
      have := k.hb
      exact IsHomLift.fac' (Tuple.projection p f n ⋙ p) k.hbase k.b)

/-- Splitting off the first coordinate and prepending it again returns the tuple, up to the
identity isomorphisms of its entries. -/
def tupleSuccToNerveFibreProductCompIso (n : ℕ) (A : Tuple p f (n + 1)) :
    (fibreProductToNerve p f n).obj ((tupleSuccToNerveFibreProduct p f n).obj A) ≅ A :=
  Stacks.Cech.tupleIso (Iso.refl A.target)
    (fun i => Fin.cases (motive := fun i =>
        ((fibreProductToNerve p f n).obj ((tupleSuccToNerveFibreProduct p f n).obj A)).source i ≅
          A.source i)
      (Iso.refl _) (fun j => Iso.refl _) i)
    (fun i => by
      cases i using Fin.cases with
      | zero =>
        change f.map (𝟙 (A.source 0)) ≫ (A.comparison 0).hom = (A.comparison 0).hom ≫ 𝟙 _
        simp
      | succ j =>
        change f.map (𝟙 (A.source j.succ)) ≫ (A.comparison j.succ).hom =
          (A.comparison j.succ).hom ≫ 𝟙 _
        simp)

/-- **The degree `n + 1` term of the Čech nerve of `f : U ⥤ X` is `U ×_X U_n`, over `C`.**
Prepending a coordinate `U ×_X U_n ⥤ U_{n + 1}` is an equivalence over `C`. -/
noncomputable def fibreProductToNerveIsEquivalenceOver (n : ℕ) :
    Functor.IsEquivalenceOver
      (TwoFibreProductOver.structureFunctor (f ⋙ p) (Tuple.projection p f n ⋙ p) p f
        (Tuple.projection p f n))
      (Tuple.projection p f (n + 1) ⋙ p) (fibreProductToNerve p f n) :=
  have := isEquivalence_fibreProductToNerve p f n
  Functor.isEquivalenceOver_of_exists_vertical_iso (fibreProductToNerve_comp_eq p f n)
    (fun A => ⟨(tupleSuccToNerveFibreProduct p f n).obj A, rfl,
      (tupleSuccToNerveFibreProductCompIso p f n A).symm,
      IsHomLift.of_fac' _ _ _ rfl rfl
        ((show p.map (𝟙 A.target) = 𝟙 _ from p.map_id _).trans (by simp; rfl))⟩)

/-- The degree `n + 1` term of the Čech nerve of `f : U ⥤ X`, with its structure functor to `C`,
is equivalent over `C` to the 2-fibre product `U ×_X U_n` with its structure functor. -/
noncomputable def tupleSuccEquivalenceOver (n : ℕ) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor (f ⋙ p) (Tuple.projection p f n ⋙ p) p f
        (Tuple.projection p f n))
      (Tuple.projection p f (n + 1) ⋙ p) :=
  StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (fibreProductToNerve_comp_eq p f n) (fibreProductToNerveIsEquivalenceOver p f n)

end Stacks.RelativeCech
