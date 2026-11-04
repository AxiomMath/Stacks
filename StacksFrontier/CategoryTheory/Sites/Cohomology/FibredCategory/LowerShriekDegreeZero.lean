module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekDeltaFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.FibreHomologyDegreeZero

/-!
# Derived lower shriek in degree zero is lower shriek

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site, as in the
standing data of Stacks 08P8, and let `Lπ_! : D(Ab(C)) ⥤ D(Ab(D))` be the left derived
lower-shriek functor of the induced morphism of topoi. This file identifies the degree-zero
member `F ↦ H^0(Lπ_!(F[0]))` of the δ-functor of Stacks 08PJ with the ordinary lower shriek
`π_!` on abelian sheaves, naturally in `F`.

## Main definitions

* `Stacks.Sites.FibredCategory.homologyHomFun` and `Stacks.Sites.FibredCategory.homologyHomEquiv`:
  for `X` in `D(A)` bounded above by zero and `Y` in `A`, the bijection
  `Hom_{D(A)}(X, Y[0]) ≃ Hom_A(H^0 X, Y)` given by degree-zero homology; that is, `H^0` is left
  adjoint to the inclusion of the heart on `D^{≤ 0}`.
* `Stacks.Sites.FibredCategory.heartHomEquiv`: the four-fold composite bijection
  `Hom(H^0(Φ(X[0])), Y) ≃ Hom(X, R Y)` for a left adjoint `Φ` of `R` on derived categories.
* `Stacks.Sites.FibredCategory.homologyDerivedAdjunction`: `X ↦ H^0(Φ(X[0]))` is a left adjoint
  of `R` whenever `Φ` is a left adjoint of the functor induced by an exact `R` and carries
  objects in degree zero to objects bounded above by zero.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyZeroAdjunction`:
  the adjunction `H^0(Lπ_!(-[0])) ⊣ π⁻¹` for the projection of a fibred category.

## Main results

* `Stacks.Sites.FibredCategory.bijective_homologyHomFun`: for `X` bounded above by zero, the map
  `Hom_{D(A)}(X, Y[0]) → Hom_A(H^0 X, Y)` given by degree-zero homology is a bijection.
* `Stacks.Sites.FibredCategory.homologyDerivedNatIso`: the degree-zero homology of a left
  derived functor is the abelian left adjoint it derives.
* `Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyZeroIso`:
  `H^0(Lπ_!(F[0])) ≅ π_! F`, naturally in `F`; this is the degree-zero comparison of Stacks 08PJ.
* `Stacks.Sites.FibredCategory.FibredCategorySituation`
  `.derivedLowerShriekHomologyZeroIsoFiberHomologySheaf`: the same comparison written against
  the sheafified presheaf of degree-zero fibre homology of Stacks 08PI, which is the form
  Stacks 08PJ compares the two δ-functors in.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08PE](https://stacks.math.columbia.edu/tag/08PE)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace Stacks.Sites.FibredCategory

universe uD vD uC vC w t t₁ t₂ v₁ u₁ v₂ u₂

section Heart

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{t₁} A]

/-- Postcomposition with an isomorphism is bijective. -/
private lemma bijective_comp_hom_of_iso {C : Type*} [Category C] {X Y Z : C} (e : Y ≅ Z) :
    Function.Bijective (fun f : X ⟶ Y ↦ f ≫ e.hom) :=
  ⟨fun _ _ h ↦ by simpa using h, fun g ↦ ⟨g ≫ e.inv, by simp⟩⟩

/-- Degree-`b` homology is bijective on morphisms from an object bounded above by `b` to an object
bounded below by `b`. -/
theorem bijective_homologyFunctor_map_of_isLE_of_isGE (X Z : DerivedCategory A) (b : ℤ)
    [X.IsLE b] [Z.IsGE b] :
    Function.Bijective (fun f : X ⟶ Z ↦ (DerivedCategory.homologyFunctor A b).map f) := by
  have h := DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    X Z b b 0 b (zero_add b) le_rfl
  have hz := bijective_comp_hom_of_iso (X := X)
    ((shiftFunctorZero (DerivedCategory A) ℤ).app Z).symm
  simpa [Function.comp_def, Functor.shiftMap, ← Functor.map_comp,
    DerivedCategory.shift_homologyFunctor] using h.comp hz

/-- The map `Hom_{D(A)}(X, Y[0]) → Hom_A(H^0 X, Y)` sending `f` to `H^0(f)` followed by the
identification of `H^0(Y[0])` with `Y`. -/
def homologyHomFun (X : DerivedCategory A) (Y : A)
    (f : X ⟶ (DerivedCategory.singleFunctor A 0).obj Y) :
    (DerivedCategory.homologyFunctor A 0).obj X ⟶ Y :=
  (DerivedCategory.homologyFunctor A 0).map f ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).hom.app Y

/-- Degree-zero homology on morphisms into the heart is contravariantly natural in the source. -/
lemma homologyHomFun_comp_left {X X' : DerivedCategory A} (g : X ⟶ X') (Y : A)
    (f : X' ⟶ (DerivedCategory.singleFunctor A 0).obj Y) :
    homologyHomFun X Y (g ≫ f) =
      (DerivedCategory.homologyFunctor A 0).map g ≫ homologyHomFun X' Y f := by
  simp [homologyHomFun]

/-- Degree-zero homology on morphisms into the heart is natural in the target. -/
lemma homologyHomFun_comp_right (X : DerivedCategory A) {Y Y' : A} (u : Y ⟶ Y')
    (f : X ⟶ (DerivedCategory.singleFunctor A 0).obj Y) :
    homologyHomFun X Y' (f ≫ (DerivedCategory.singleFunctor A 0).map u) =
      homologyHomFun X Y f ≫ u := by
  have h := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).hom.naturality u
  dsimp at h
  simp [homologyHomFun, h]

/-- For `X` with no cohomology in positive degrees, degree-zero homology is a bijection
`Hom_{D(A)}(X, Y[0]) → Hom_A(H^0 X, Y)`. -/
theorem bijective_homologyHomFun (X : DerivedCategory A) [X.IsLE 0] (Y : A) :
    Function.Bijective (homologyHomFun X Y) := by
  have hb := bijective_homologyFunctor_map_of_isLE_of_isGE X
    ((DerivedCategory.singleFunctor A 0).obj Y) 0
  exact (bijective_comp_hom_of_iso (X := (DerivedCategory.homologyFunctor A 0).obj X)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).app Y)).comp hb

/-- The bijection `Hom_{D(A)}(X, Y[0]) ≃ Hom_A(H^0 X, Y)` given by degree-zero homology, for `X`
bounded above by zero. -/
def homologyHomEquiv (X : DerivedCategory A) [X.IsLE 0] (Y : A) :
    (X ⟶ (DerivedCategory.singleFunctor A 0).obj Y) ≃
      ((DerivedCategory.homologyFunctor A 0).obj X ⟶ Y) :=
  Equiv.ofBijective _ (bijective_homologyHomFun X Y)

/-- The bijection of the heart is degree-zero homology. -/
@[simp]
lemma homologyHomEquiv_apply (X : DerivedCategory A) [X.IsLE 0] (Y : A)
    (f : X ⟶ (DerivedCategory.singleFunctor A 0).obj Y) :
    homologyHomEquiv X Y f = homologyHomFun X Y f := rfl

/-- The bijection of the heart is contravariantly natural in the source. -/
lemma homologyHomEquiv_comp_left {X X' : DerivedCategory A} [X.IsLE 0] [X'.IsLE 0]
    (g : X ⟶ X') (Y : A) (f : X' ⟶ (DerivedCategory.singleFunctor A 0).obj Y) :
    homologyHomEquiv X Y (g ≫ f) =
      (DerivedCategory.homologyFunctor A 0).map g ≫ homologyHomEquiv X' Y f :=
  homologyHomFun_comp_left g Y f

/-- The inverse of the bijection of the heart is natural in the target. -/
lemma homologyHomEquiv_symm_comp_right (X : DerivedCategory A) [X.IsLE 0] {Y Y' : A}
    (u : (DerivedCategory.homologyFunctor A 0).obj X ⟶ Y) (g : Y ⟶ Y') :
    (homologyHomEquiv X Y').symm (u ≫ g) =
      (homologyHomEquiv X Y).symm u ≫ (DerivedCategory.singleFunctor A 0).map g := by
  apply (homologyHomEquiv X Y').injective
  rw [Equiv.apply_symm_apply, homologyHomEquiv_apply, homologyHomFun_comp_right,
    ← homologyHomEquiv_apply, Equiv.apply_symm_apply]

end Heart

section DerivedAdjunction

variable {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{t₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{t₂} A₂]
  (Φ : DerivedCategory A₁ ⥤ DerivedCategory A₂) (R : A₂ ⥤ A₁)
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (adj : Φ ⊣ R.mapDerivedCategory)
  [hLE : ∀ X : A₁, (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)).IsLE 0]

/-- For `Φ` a left adjoint of the functor induced on derived categories by an exact `R`, carrying
objects in degree zero to objects with no cohomology in positive degrees, the composite of the four
bijections `Hom(H^0(Φ(X[0])), Y) ≃ Hom(Φ(X[0]), Y[0]) ≃ Hom(X[0], R(Y[0]))` and
`Hom(X[0], R(Y[0])) ≃ Hom(X[0], (R Y)[0]) ≃ Hom(X, R Y)`. -/
def heartHomEquiv (X : A₁) (Y : A₂) :
    ((DerivedCategory.homologyFunctor A₂ 0).obj
        (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)) ⟶ Y) ≃ (X ⟶ R.obj Y) :=
  (homologyHomEquiv (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)) Y).symm.trans
    ((adj.homEquiv _ _).trans
      (((R.mapDerivedCategorySingleFunctor 0).app Y).homToEquiv.trans
        (Functor.FullyFaithful.ofFullyFaithful
          (DerivedCategory.singleFunctor A₁ 0)).homEquiv.symm))

/-- The value of `heartHomEquiv` on a morphism `H^0(Φ(X[0])) ⟶ Y`. -/
lemma heartHomEquiv_apply (X : A₁) (Y : A₂)
    (f : (DerivedCategory.homologyFunctor A₂ 0).obj
      (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)) ⟶ Y) :
    heartHomEquiv Φ R adj X Y f =
      (Functor.FullyFaithful.ofFullyFaithful
          (DerivedCategory.singleFunctor A₁ 0)).preimage
        ((adj.homEquiv _ _)
            ((homologyHomEquiv (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)) Y).symm f) ≫
          (R.mapDerivedCategorySingleFunctor 0).hom.app Y) := rfl

/-- The value of the inverse of `heartHomEquiv` on a morphism `X ⟶ R Y`. -/
lemma heartHomEquiv_symm_apply (X : A₁) (Y : A₂) (c : X ⟶ R.obj Y) :
    (heartHomEquiv Φ R adj X Y).symm c =
      homologyHomEquiv (Φ.obj ((DerivedCategory.singleFunctor A₁ 0).obj X)) Y
        ((adj.homEquiv _ _).symm
          ((DerivedCategory.singleFunctor A₁ 0).map c ≫
            (R.mapDerivedCategorySingleFunctor 0).inv.app Y)) := rfl

/-- The functor `X ↦ H^0(Φ(X[0]))` is left adjoint to `R`, with the bijections `heartHomEquiv` on
morphisms. -/
def homologyDerivedAdjunction :
    DerivedCategory.singleFunctor A₁ 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor A₂ 0 ⊣ R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := heartHomEquiv Φ R adj
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        rw [heartHomEquiv_symm_apply, heartHomEquiv_symm_apply, Functor.map_comp,
          Category.assoc, Adjunction.homEquiv_naturality_left_symm,
          homologyHomEquiv_comp_left]
        rfl
      homEquiv_naturality_right := by
        intro X Y Y' f g
        rw [heartHomEquiv_apply, heartHomEquiv_apply, homologyHomEquiv_symm_comp_right,
          Adjunction.homEquiv_naturality_right, Category.assoc]
        have hnat := (R.mapDerivedCategorySingleFunctor 0).hom.naturality g
        dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
        rw [hnat, ← Category.assoc, Functor.FullyFaithful.preimage_comp]
        simp }

/-- If `L` is a left adjoint of `R` on the abelian categories, the functor `X ↦ H^0(Φ(X[0]))` is
naturally isomorphic to `L`. -/
def homologyDerivedNatIso (L : A₁ ⥤ A₂) (adj₀ : L ⊣ R) :
    DerivedCategory.singleFunctor A₁ 0 ⋙ Φ ⋙ DerivedCategory.homologyFunctor A₂ 0 ≅ L :=
  (homologyDerivedAdjunction Φ R adj).leftAdjointUniq adj₀

end DerivedAdjunction

namespace FibredCategorySituation

section Derived

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w})

attribute [local instance] HasDerivedCategory.standard

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC})
    (ComplexShape.up ℤ))]

/-- The adjunction `H^0(Lπ_!(-[0])) ⊣ π⁻¹`: the degree-zero cohomology of derived lower shriek is
left adjoint to the inverse image of abelian sheaves. -/
def derivedLowerShriekHomologyZeroAdjunction (h : s.AbelianLowerShriekAcyclic) :
    s.derivedAbelianLowerShriekHomology 0 ⊣ s.abelianInverseImage := by
  letI : ∀ X : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC},
      (s.derivedAbelianLowerShriek.obj
        ((DerivedCategory.singleFunctor _ 0).obj X)).IsLE 0 :=
    s.isLE_derivedAbelianLowerShriek_obj_single h
  exact homologyDerivedAdjunction s.derivedAbelianLowerShriek
    (Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{max w uD vD uC, vC, uC, vD, uD}
      s.topology s.base.J s.p)
    (s.derivedAbelianLowerShriekAdjunction h)

/-- The degree-zero member `F ↦ H^0(Lπ_! F)` of the homological δ-functor of derived lower shriek
is the ordinary lower shriek `π_!` on abelian sheaves, naturally in `F`. -/
def derivedLowerShriekHomologyZeroIso (h : s.AbelianLowerShriekAcyclic) :
    s.derivedAbelianLowerShriekHomology 0 ≅ s.abelianLowerShriek := by
  letI : ∀ X : Sheaf s.topology AddCommGrpCat.{max w uD vD uC vC},
      (s.derivedAbelianLowerShriek.obj
        ((DerivedCategory.singleFunctor _ 0).obj X)).IsLE 0 :=
    s.isLE_derivedAbelianLowerShriek_obj_single h
  exact homologyDerivedNatIso s.derivedAbelianLowerShriek
    (Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{max w uD vD uC, vC, uC, vD, uD}
      s.topology s.base.J s.p)
    (s.derivedAbelianLowerShriekAdjunction h) s.abelianLowerShriek
    s.abelianLowerShriekAdjunction

end Derived

section FibreHomology

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})

attribute [local instance] HasDerivedCategory.standard

variable [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
  (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC})
    (ComplexShape.up ℤ))]

/-- The degree-zero member of the δ-functor of derived lower shriek is the sheafification of the
presheaf `L_{0,p}` of degree-zero fibre homology, naturally in the abelian sheaf. -/
def derivedLowerShriekHomologyZeroIsoFiberHomologySheaf (h : s.AbelianLowerShriekAcyclic) :
    s.derivedAbelianLowerShriekHomology 0 ≅
      sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC} ⋙
        fiberHomologyPresheafFunctor s 0 ⋙
          presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC} :=
  s.derivedLowerShriekHomologyZeroIso h ≪≫ abelianLowerShriekIsoFiberHomologySheafZero s

end FibreHomology

end FibredCategorySituation

end Stacks.Sites.FibredCategory

end
