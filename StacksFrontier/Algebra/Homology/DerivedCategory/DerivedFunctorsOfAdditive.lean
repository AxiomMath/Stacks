module

import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedDerivedFunctorComparison
public import StacksFrontier.CategoryTheory.Functor.Derived.Morphisms

/-!
# The derived functors of an additive functor, and acyclic objects

Let `F : A ⥤ B` be an additive functor between abelian categories (Situation 05T4). It induces
`F : K(A) ⥤ D(B)`, `F⁺ : K⁺(A) ⥤ D⁺(B)` and `F⁻ : K⁻(A) ⥤ D⁻(B)`, the induced functors on homotopy
categories followed by the localization of `K(B)`, and these lead to four derived functors.

* The right derived functors of `F` are the partial functors `RF` of `F : K(A) ⥤ D(B)` relative
  to `Qis(A)`, and of `F⁺ : K⁺(A) ⥤ D⁺(B)` relative to `Qis⁺(A)`.
* The left derived functors of `F` are the partial functors `LF` of `F : K(A) ⥤ D(B)` relative
  to `Qis(A)`, and of `F⁻ : K⁻(A) ⥤ D⁻(B)` relative to `Qis⁻(A)`.
* An object `X` of `A` is right acyclic for `F` if `X[0]` computes `RF`, and left acyclic for `F`
  if `X[0]` computes `LF`.

## Main definitions

* `CategoryTheory.Functor.rightDerivedDomain`, `CategoryTheory.Functor.leftDerivedDomain`: the
  objects at which `RF`, resp. `LF`, is defined (Stacks 05S9).
* `CategoryTheory.Functor.rightDerivedPartial`, `CategoryTheory.Functor.leftDerivedPartial`: the
  partial functor `RF`, resp. `LF`, on the full subcategory of objects at which it is defined,
  acting on morphisms by the maps of Stacks 05SA.
* `CategoryTheory.Functor.rightDerivedK`, `CategoryTheory.Functor.rightDerivedKPlus`: the right
  derived functors of `F`, cases (1) and (2) of Situation 05T4.
* `CategoryTheory.Functor.leftDerivedK`, `CategoryTheory.Functor.leftDerivedKMinus`: the left
  derived functors of `F`, cases (3) and (4) of Situation 05T4.
* `CategoryTheory.Functor.IsRightAcyclic`, `CategoryTheory.Functor.IsLeftAcyclic`: right and left
  acyclic objects.

## Main results

* `CategoryTheory.Functor.isRightAcyclic_iff_computesRightDerived_K`: an object is right acyclic
  whether `RF` is taken on `K⁺(A)` or on `K(A)` (Stacks 05T5(2)).
* `CategoryTheory.Functor.isLeftAcyclic_iff_computesLeftDerived_K`: an object is left acyclic
  whether `LF` is taken on `K⁻(A)` or on `K(A)` (Stacks 05T5(4)).

## Implementation notes

"Defined at", the value and "computes" are those of Stacks 05S9 and 05SX:
`Functor.IsRightDerivedValueAt`, `Functor.ComputesRightDerived` and their duals, an
essentially constant ind-object, resp. pro-object, on `X/S`, resp. `S/X`. A partial functor is a
functor defined on a subcategory; here the subcategory is the full subcategory of the objects at
which the derived functor is defined, its value at an object is a chosen value there, and its
value at a morphism is the unique morphism of Stacks 05SA compatible with the structure maps of
the two values. Nothing beyond `F` additive and `A`, `B` abelian is assumed: the derived functors
need not be everywhere defined, and `D(A)` is not used. The multiplicative systems are the
quasi-isomorphisms of the source `A`, never of `B`. The functors `F`, `F⁺`, `F⁻`, the categories
`K⁻(A)`, `D⁺(B)`, `D⁻(B)` and the systems `Qis(A)`, `Qis⁺(A)`, `Qis⁻(A)` are those of
`StacksDerivedFunctorComparison` (Stacks 05T5).

The source says that `X` is right acyclic if `X[0]` computes `RF` without saying which of the two
right derived functors is meant; by Stacks 05T5 the two conditions agree, and the definition uses
`RF` on `K⁺(A)`, the other being `isRightAcyclic_iff_computesRightDerived_K`. Likewise for left
acyclic objects with `K⁻(A)` and `K(A)`.

## References

* [Stacks, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks, Tag 05T4](https://stacks.math.columbia.edu/tag/05T4)
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

section Partial

variable {𝒟 : Type u₁} [Category.{v₁} 𝒟] {𝒟' : Type u₂} [Category.{v₂} 𝒟']
  (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟)

/-- The objects of `𝒟` at which the right derived functor `RF` of `F` relative to `S` is defined
(Stacks 05S9): those `X` at which the ind-object `X/S ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')` is
essentially constant. -/
def rightDerivedDomain : ObjectProperty 𝒟 := fun X ↦ ∃ c, F.IsRightDerivedValueAt S X c

/-- The objects of `𝒟` at which the left derived functor `LF` of `F` relative to `S` is defined
(Stacks 05S9): those `X` at which the pro-object `S/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')` is
essentially constant. -/
def leftDerivedDomain : ObjectProperty 𝒟 := fun X ↦ ∃ c, F.IsLeftDerivedValueAt S X c

open StacksDerivedFunctor

section Right

variable [S.HasLeftCalculusOfFractions]

/-- The map `RF(𝟙 X)` of Stacks 05SA between a value of `RF` at `X` and itself is the identity. -/
lemma rightDerivedMap_id {X : 𝒟}
    {c : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : F.IsRightDerivedValueAt S X c) :
    rightDerivedMap S F h h (𝟙 X) = 𝟙 c.pt := by
  symm
  refine rightDerivedMap_unique S F h h (𝟙 X) _ fun X' Y' s s' f' hs hs' hsq ↦ ?_
  refine (Category.comp_id _).trans ?_
  exact (underS_cocone_nat S F c (s := MorphismProperty.Under.mk ⊤ s hs)
    (t := MorphismProperty.Under.mk ⊤ s' hs') f'
    (show s ≫ f' = s' by rw [← hsq, Category.id_comp])).symm

/-- The maps `RF(f)` of Stacks 05SA are compatible with composition. -/
lemma rightDerivedMap_comp {X Y Z : 𝒟}
    {cX : Cocone (MorphismProperty.Under.forget S ⊤ X ⋙ Under.forget X ⋙ F)}
    {cY : Cocone (MorphismProperty.Under.forget S ⊤ Y ⋙ Under.forget Y ⋙ F)}
    {cZ : Cocone (MorphismProperty.Under.forget S ⊤ Z ⋙ Under.forget Z ⋙ F)}
    (hX : F.IsRightDerivedValueAt S X cX) (hY : F.IsRightDerivedValueAt S Y cY)
    (hZ : F.IsRightDerivedValueAt S Z cZ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedMap S F hX hZ (f ≫ g) =
      rightDerivedMap S F hX hY f ≫ rightDerivedMap S F hY hZ g := by
  symm
  refine rightDerivedMap_unique S F hX hZ (f ≫ g) _ fun X' Z' s s'' h' hs hs'' hsq ↦ ?_
  obtain ⟨Y₁, s'₁, f₁, hs'₁, hsq₁⟩ := exists_ore_square_left S f s hs
  obtain ⟨Z₁, s''₁, g₁, hs''₁, hsq₂⟩ := exists_ore_square_left S g s'₁ hs'₁
  have e₁ := rightDerivedMap_spec S F hX hY f X' Y₁ s s'₁ f₁ hs hs'₁ hsq₁
  have e₂ := rightDerivedMap_spec S F hY hZ g Y₁ Z₁ s'₁ s''₁ g₁ hs'₁ hs''₁ hsq₂
  have e₃ := indep_RF S F (f ≫ g) cZ s hs s''₁ s'' hs''₁ hs'' (f₁ ≫ g₁) h'
    (by rw [Category.assoc, hsq₂, ← Category.assoc, hsq₁, Category.assoc]) hsq
  exact (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ rightDerivedMap S F hY hZ g) e₁).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (F.map f₁ ≫ ·) e₂).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ cZ.ι.app (MorphismProperty.Under.mk ⊤ s''₁ hs''₁))
      (F.map_comp f₁ g₁).symm).trans e₃

/-- **The partial functor `RF`** (Stacks 05S9, 05SA). The right derived functor of `F` relative
to the multiplicative system `S`, as a functor on the full subcategory of the objects at which it
is defined: its value at `X` is a chosen value `RF(X)` of the essentially constant ind-object
`(s : X ⟶ X') ↦ F(X')`, and its value at `f : X ⟶ Y` is the unique `RF(f)` compatible with the
structure maps of the two values. -/
noncomputable def rightDerivedPartial : (F.rightDerivedDomain S).FullSubcategory ⥤ 𝒟' where
  obj X := X.property.choose.pt
  map {X Y} f := rightDerivedMap S F X.property.choose_spec Y.property.choose_spec f.hom
  map_id X := rightDerivedMap_id F S X.property.choose_spec
  map_comp {X Y Z} f g := rightDerivedMap_comp F S X.property.choose_spec
    Y.property.choose_spec Z.property.choose_spec f.hom g.hom

/-- The value of the partial functor `rightDerivedPartial F S` at `X` is a value of `RF` at `X`:
the structure maps `F(X') ⟶ RF(X)` exhibit the ind-object as essentially constant with value
`(F.rightDerivedPartial S).obj X`. -/
lemma isRightDerivedValueAt_rightDerivedPartial (X : (F.rightDerivedDomain S).FullSubcategory) :
    ∃ c : Cocone (MorphismProperty.Under.forget S ⊤ X.obj ⋙ Under.forget X.obj ⋙ F),
      F.IsRightDerivedValueAt S X.obj c ∧ c.pt = (F.rightDerivedPartial S).obj X :=
  ⟨X.property.choose, X.property.choose_spec, rfl⟩

end Right

section Left

variable [S.HasRightCalculusOfFractions]

/-- The map `LF(𝟙 X)` of Stacks 05SA between a value of `LF` at `X` and itself is the identity. -/
lemma leftDerivedMap_id {X : 𝒟}
    {c : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)}
    (h : F.IsLeftDerivedValueAt S X c) :
    leftDerivedMap S F h h (𝟙 X) = 𝟙 c.pt := by
  symm
  refine leftDerivedMap_unique S F h h (𝟙 X) _ fun X' Y' s s' f' hs hs' hsq ↦ ?_
  refine (Category.id_comp _).trans ?_
  exact (overS_cone_nat S F c (s := MorphismProperty.Over.mk ⊤ s hs)
    (t := MorphismProperty.Over.mk ⊤ s' hs') f'
    (show f' ≫ s' = s by rw [← hsq, Category.comp_id])).symm

/-- The maps `LF(f)` of Stacks 05SA are compatible with composition. -/
lemma leftDerivedMap_comp {X Y Z : 𝒟}
    {dX : Cone (MorphismProperty.Over.forget S ⊤ X ⋙ Over.forget X ⋙ F)}
    {dY : Cone (MorphismProperty.Over.forget S ⊤ Y ⋙ Over.forget Y ⋙ F)}
    {dZ : Cone (MorphismProperty.Over.forget S ⊤ Z ⋙ Over.forget Z ⋙ F)}
    (hX : F.IsLeftDerivedValueAt S X dX) (hY : F.IsLeftDerivedValueAt S Y dY)
    (hZ : F.IsLeftDerivedValueAt S Z dZ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedMap S F hX hZ (f ≫ g) =
      leftDerivedMap S F hX hY f ≫ leftDerivedMap S F hY hZ g := by
  symm
  refine leftDerivedMap_unique S F hX hZ (f ≫ g) _ fun X' Z' s s'' h' hs hs'' hsq ↦ ?_
  obtain ⟨Y₁, g₁, t₁, ht₁, hsq₁⟩ := exists_ore_square_right S s'' g hs''
  obtain ⟨X₁, f₁, t₂, ht₂, hsq₂⟩ := exists_ore_square_right S t₁ f ht₁
  have e₁ := leftDerivedMap_spec S F hY hZ g Y₁ Z' t₁ s'' g₁ ht₁ hs'' hsq₁.symm
  have e₂ := leftDerivedMap_spec S F hX hY f X₁ Y₁ t₂ t₁ f₁ ht₂ ht₁ hsq₂.symm
  have e₃ := indep_LF S F (f ≫ g) dX s'' hs'' t₂ s ht₂ hs (f₁ ≫ g₁) h'
    (by rw [← Category.assoc, ← hsq₂, Category.assoc, ← hsq₁, Category.assoc]) hsq
  exact (Category.assoc _ _ _).trans <|
    (congrArg (leftDerivedMap S F hX hY f ≫ ·) e₁).trans <| (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ F.map g₁) e₂).trans <| (Category.assoc _ _ _).trans <|
    (congrArg (dX.π.app (MorphismProperty.Over.mk ⊤ t₂ ht₂) ≫ ·)
      (F.map_comp f₁ g₁).symm).trans e₃

/-- **The partial functor `LF`** (Stacks 05S9, 05SA). The left derived functor of `F` relative
to the multiplicative system `S`, as a functor on the full subcategory of the objects at which it
is defined: its value at `X` is a chosen value `LF(X)` of the essentially constant pro-object
`(s : X' ⟶ X) ↦ F(X')`, and its value at `f : X ⟶ Y` is the unique `LF(f)` compatible with the
structure maps of the two values. -/
noncomputable def leftDerivedPartial : (F.leftDerivedDomain S).FullSubcategory ⥤ 𝒟' where
  obj X := X.property.choose.pt
  map {X Y} f := leftDerivedMap S F X.property.choose_spec Y.property.choose_spec f.hom
  map_id X := leftDerivedMap_id F S X.property.choose_spec
  map_comp {X Y Z} f g := leftDerivedMap_comp F S X.property.choose_spec
    Y.property.choose_spec Z.property.choose_spec f.hom g.hom

/-- The value of the partial functor `leftDerivedPartial F S` at `X` is a value of `LF` at `X`. -/
lemma isLeftDerivedValueAt_leftDerivedPartial (X : (F.leftDerivedDomain S).FullSubcategory) :
    ∃ c : Cone (MorphismProperty.Over.forget S ⊤ X.obj ⋙ Over.forget X.obj ⋙ F),
      F.IsLeftDerivedValueAt S X.obj c ∧ c.pt = (F.leftDerivedPartial S).obj X :=
  ⟨X.property.choose, X.property.choose_spec, rfl⟩

end Left

end Partial

section Additive

open StacksDerivedFunctorComparison

variable {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]

/-- The quasi-isomorphisms `Qis(A)` of `K(A)` admit a calculus of left fractions. -/
lemma hasLeftCalculusOfFractions_qisBig : (qisBig A).HasLeftCalculusOfFractions := by
  rw [qisBig, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- The quasi-isomorphisms `Qis(A)` of `K(A)` admit a calculus of right fractions. -/
lemma hasRightCalculusOfFractions_qisBig : (qisBig A).HasRightCalculusOfFractions := by
  rw [qisBig, HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

/-- The quasi-isomorphisms `Qis⁺(A)` of `K⁺(A)` admit a calculus of left fractions. -/
lemma hasLeftCalculusOfFractions_qisPlus : (qisPlus A).HasLeftCalculusOfFractions := by
  rw [qisPlus, HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
  infer_instance

/-- `Qis⁻(A)` is the class of morphisms of `K⁻(A)` whose cone is acyclic. -/
lemma qisMinus_eq_trW :
    qisMinus A =
      ((HomotopyCategory.subcategoryAcyclic A).inverseImage (HomotopyCategory.Minus.ι A)).trW := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff, ← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  rfl

/-- The quasi-isomorphisms `Qis⁻(A)` of `K⁻(A)` admit a calculus of right fractions. -/
lemma hasRightCalculusOfFractions_qisMinus : (qisMinus A).HasRightCalculusOfFractions := by
  rw [qisMinus_eq_trW]
  infer_instance

variable (A) in
/-- The functor `A ⥤ K⁻(A)`, `X ↦ X[n]`, placing an object in degree `n`. -/
noncomputable def singleFunctorKMinus (n : ℤ) : A ⥤ KMinus A :=
  (HomotopyCategory.minus A).lift (HomotopyCategory.singleFunctor A n) fun X ↦ by
    rw [← HomotopyCategory.quotient_obj_singleFunctors_obj, HomotopyCategory.minus_quotient_obj_iff]
    exact ⟨n, inferInstance⟩

variable [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- **Stacks 0157(1), case (1) of Situation 05T4.** A right derived functor of the additive
functor `F : A ⥤ B`: the partial functor `RF` of `F : K(A) ⥤ D(B)` relative to the
quasi-isomorphisms `Qis(A)`, defined on the full subcategory of the objects of `K(A)` at which it
is defined. -/
@[stacks 0157 "(1), the right derived functor `RF` of case (1) of 05T4: `F : K(A) ⥤ D(B)` relative
to `Qis(A)`, a functor on the objects where it is defined"]
noncomputable def rightDerivedK :
    ((Fbig F).rightDerivedDomain (qisBig A)).FullSubcategory ⥤ DerivedCategory B :=
  haveI := hasLeftCalculusOfFractions_qisBig (A := A)
  (Fbig F).rightDerivedPartial (qisBig A)

/-- **Stacks 0157(1), case (2) of Situation 05T4.** A right derived functor of the additive
functor `F : A ⥤ B`: the partial functor `RF` of `F⁺ : K⁺(A) ⥤ D⁺(B)` relative to the
quasi-isomorphisms `Qis⁺(A)`, defined on the full subcategory of the objects of `K⁺(A)` at which
it is defined. -/
@[stacks 0157 "(1), the right derived functor `RF` of case (2) of 05T4: `F : K⁺(A) ⥤ D⁺(B)`
relative to `Qis⁺(A)`, a functor on the objects where it is defined"]
noncomputable def rightDerivedKPlus :
    ((Fplus F).rightDerivedDomain (qisPlus A)).FullSubcategory ⥤ Dplus B :=
  haveI := hasLeftCalculusOfFractions_qisPlus (A := A)
  (Fplus F).rightDerivedPartial (qisPlus A)

/-- **Stacks 0157(2), case (3) of Situation 05T4.** A left derived functor of the additive
functor `F : A ⥤ B`: the partial functor `LF` of `F : K(A) ⥤ D(B)` relative to the
quasi-isomorphisms `Qis(A)`, defined on the full subcategory of the objects of `K(A)` at which it
is defined. -/
@[stacks 0157 "(2), the left derived functor `LF` of case (3) of 05T4: `F : K(A) ⥤ D(B)` relative
to `Qis(A)`, a functor on the objects where it is defined"]
noncomputable def leftDerivedK :
    ((Fbig F).leftDerivedDomain (qisBig A)).FullSubcategory ⥤ DerivedCategory B :=
  haveI := hasRightCalculusOfFractions_qisBig (A := A)
  (Fbig F).leftDerivedPartial (qisBig A)

/-- **Stacks 0157(2), case (4) of Situation 05T4.** A left derived functor of the additive
functor `F : A ⥤ B`: the partial functor `LF` of `F⁻ : K⁻(A) ⥤ D⁻(B)` relative to the
quasi-isomorphisms `Qis⁻(A)`, defined on the full subcategory of the objects of `K⁻(A)` at which
it is defined. -/
@[stacks 0157 "(2), the left derived functor `LF` of case (4) of 05T4: `F : K⁻(A) ⥤ D⁻(B)`
relative to `Qis⁻(A)`, a functor on the objects where it is defined"]
noncomputable def leftDerivedKMinus :
    ((Fminus F).leftDerivedDomain (qisMinus A)).FullSubcategory ⥤ Dminus B :=
  haveI := hasRightCalculusOfFractions_qisMinus (A := A)
  (Fminus F).leftDerivedPartial (qisMinus A)

/-- **Stacks 0157(3).** An object `X` of `A` is *right acyclic for `F`*, or *acyclic for `RF`*,
if `X[0]` computes `RF`: the right derived functor of `F⁺ : K⁺(A) ⥤ D⁺(B)` relative to
`Qis⁺(A)` is defined at `X[0]` and the canonical map `F(X[0]) ⟶ RF(X[0])` is an isomorphism
(Stacks 05SX). -/
@[stacks 0157 "(3), right acyclic objects: `X[0]` computes `RF`; for `RF` on `K(A)` this is
`isRightAcyclic_iff_computesRightDerived_K`"]
def IsRightAcyclic : ObjectProperty A := fun X ↦
  (Fplus F).ComputesRightDerived (qisPlus A) ((HomotopyCategory.Plus.singleFunctor A 0).obj X)

/-- **Stacks 0157(3), the two right derived functors.** `X` is right acyclic for `F` exactly
when `X[0]` computes the right derived functor of `F : K(A) ⥤ D(B)` relative to `Qis(A)`. -/
@[stacks 0157 "(3), with `RF` the right derived functor of case (1) of 05T4"]
theorem isRightAcyclic_iff_computesRightDerived_K (X : A) :
    F.IsRightAcyclic X ↔
      (Fbig F).ComputesRightDerived (qisBig A) ((HomotopyCategory.singleFunctor A 0).obj X) :=
  (computesR_big_iff_plus F ((HomotopyCategory.Plus.singleFunctor A 0).obj X)).symm

/-- **Stacks 0157(4).** An object `X` of `A` is *left acyclic for `F`*, or *acyclic for `LF`*,
if `X[0]` computes `LF`: the left derived functor of `F⁻ : K⁻(A) ⥤ D⁻(B)` relative to
`Qis⁻(A)` is defined at `X[0]` and the canonical map `LF(X[0]) ⟶ F(X[0])` is an isomorphism
(Stacks 05SX). -/
@[stacks 0157 "(4), left acyclic objects: `X[0]` computes `LF`; for `LF` on `K(A)` this is
`isLeftAcyclic_iff_computesLeftDerived_K`"]
def IsLeftAcyclic : ObjectProperty A := fun X ↦
  (Fminus F).ComputesLeftDerived (qisMinus A) ((singleFunctorKMinus A 0).obj X)

/-- **Stacks 0157(4), the two left derived functors.** `X` is left acyclic for `F` exactly when
`X[0]` computes the left derived functor of `F : K(A) ⥤ D(B)` relative to `Qis(A)`. -/
@[stacks 0157 "(4), with `LF` the left derived functor of case (3) of 05T4"]
theorem isLeftAcyclic_iff_computesLeftDerived_K (X : A) :
    F.IsLeftAcyclic X ↔
      (Fbig F).ComputesLeftDerived (qisBig A) ((HomotopyCategory.singleFunctor A 0).obj X) :=
  (computesL_big_iff_minus F ((singleFunctorKMinus A 0).obj X)).symm

end Additive

end CategoryTheory.Functor
