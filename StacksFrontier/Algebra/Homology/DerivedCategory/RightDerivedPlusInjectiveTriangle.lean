module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import StacksFrontier.Algebra.Homology.DerivedFunctorLongExact
public import StacksFrontier.Homology.DerivedCategory.RightDerivedInjectiveModel

/-!
# Distinguished triangles of right derived functors on `D⁺` from short exact sequences on injectives

Let `F ⟶ G ⟶ H` be a short complex of additive functors `C ⥤ D` between abelian categories which
is short exact at every injective object of `C`.  `CategoryTheory.triangleOfInjectiveCochainComplex`
of `StacksFrontier/Algebra/Homology/DerivedFunctorLongExact.lean` turns it into a distinguished
triangle
`F(K) ⟶ G(K) ⟶ H(K) ⟶ F(K)[1]` for every cochain complex `K` of injective objects.  This file
supplies the comparisons that identify the vertices of that triangle with values of the right
derived functors `RF`, `RG`, `RH : D⁺(C) ⥤ D⁺(D)`, and with values of the right derived functor of
a further functor precomposed with an exact functor preserving injective objects.

## Main definitions

* `Stacks.RightDerivedPlusTriangle.qIsoRightDerivedFunctorPlus`: for a bounded below complex `J` of
  injective objects with `J ≅ X` in `D⁺(C)`, the comparison `G(J) ≅ RG(X)` in `D(D)`.
* `Stacks.RightDerivedPlusTriangle.restrictInjectiveObject`: an additive functor preserving
  injective objects, on injective objects.
* `Stacks.RightDerivedPlusTriangle.qIsoRightDerivedFunctorPlusOfExact`: for `r : C ⥤ C'` exact and
  preserving injective objects, the comparison `G(r(J)) ≅ RG(r(X))`, `X` a single object.
* `Stacks.RightDerivedPlusTriangle.mapHomologicalComplexBiprodIso`: a biproduct of additive
  functors applied to a complex is the biproduct of the two complexes.

## Main results

* `Stacks.RightDerivedPlusTriangle.exists_distinguished_of_iso`: a triangle whose three vertices
  are isomorphic to those of a distinguished triangle can be completed to a distinguished triangle
  on its own vertices.

## References

* [Stacks Project, Tag 05TA](https://stacks.math.columbia.edu/tag/05TA)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' w'' v u v' u' v'' u''

namespace Stacks.RightDerivedPlusTriangle

section Pretriangulated

variable {T : Type u} [Category.{v} T] [HasZeroObject T] [HasShift T ℤ] [Preadditive T]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]

/-- **A distinguished triangle can be moved onto isomorphic vertices.**  If the three vertices of a
distinguished triangle are isomorphic to `A`, `B` and `C`, there is a distinguished triangle
`A ⟶ B ⟶ C ⟶ A[1]`. -/
theorem exists_distinguished_of_iso (Δ : Triangle T) (hΔ : Δ ∈ distTriang T) {A B C : T}
    (e₁ : A ≅ Δ.obj₁) (e₂ : B ≅ Δ.obj₂) (e₃ : C ≅ Δ.obj₃) :
    ∃ (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ A⟦(1 : ℤ)⟧), Triangle.mk a b c ∈ distTriang T := by
  refine ⟨e₁.hom ≫ Δ.mor₁ ≫ e₂.inv, e₂.hom ≫ Δ.mor₂ ≫ e₃.inv,
    e₃.hom ≫ Δ.mor₃ ≫ (shiftFunctor T (1 : ℤ)).map e₁.inv, ?_⟩
  refine isomorphic_distinguished _ hΔ _ (Triangle.isoMk _ _ e₁ e₂ e₃ ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

end Pretriangulated

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]

/-- **A right derived functor on `D⁺` is computed on a bounded below complex of injectives
isomorphic to the object**: for `J` such a complex and `e : J ≅ X` in `D⁺(C)`, the image of
`G(J)` in `D(D)` is `RG(X)`. -/
def qIsoRightDerivedFunctorPlus (G : C ⥤ D) [G.Additive]
    (J : CochainComplex.Plus (InjectiveObject C)) {X : DerivedCategory.Plus C}
    (e : DerivedCategory.Plus.Q.obj ((InjectiveObject.ι C).mapCochainComplexPlus.obj J) ≅ X) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj)) ≅
      DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj X) :=
  DerivedCategory.Plus.ι.mapIso ((Stacks.InjectiveModel.plusQhIsoPlusQ (G.mapCochainComplexPlus.obj
      ((InjectiveObject.ι C).mapCochainComplexPlus.obj J))).symm ≪≫
    Stacks.InjectiveModel.rightDerivedFunctorPlusUnitIso G J ≪≫
    G.rightDerivedFunctorPlus.mapIso
      (Stacks.InjectiveModel.plusQhIsoPlusQ ((InjectiveObject.ι C).mapCochainComplexPlus.obj J) ≪≫
        e))

variable {C' : Type u''} [Category.{v''} C'] [Abelian C'] [HasDerivedCategory.{w''} C']
  [EnoughInjectives C'] (r : C ⥤ C') [r.Additive] [r.PreservesInjectiveObjects]

/-- An additive functor preserving injective objects, as a functor between the categories of
injective objects. -/
abbrev restrictInjectiveObject : InjectiveObject C ⥤ InjectiveObject C' :=
  ObjectProperty.lift _ (InjectiveObject.ι C ⋙ r) (fun X ↦ by
    have : Injective X.obj := X.property
    exact (inferInstance : Injective (r.obj X.obj)))

/-- The functor `restrictInjectiveObject` is additive. -/
instance additive_restrictInjectiveObject : (restrictInjectiveObject r).Additive :=
  have : (restrictInjectiveObject r ⋙ InjectiveObject.ι C').Additive :=
    inferInstanceAs (InjectiveObject.ι C ⋙ r).Additive
  Functor.additive_of_comp_faithful _ (InjectiveObject.ι C')

variable [PreservesFiniteLimits r] [PreservesFiniteColimits r]

/-- **An exact functor carries an injective model of a single object to an injective model of its
image**: if `J ≅ F` in `D⁺(C)`, with `J` a bounded below complex of injectives and `F` placed in
degree `0`, then `r(J) ≅ r(F)` in `D⁺(C')`. -/
def restrictInjectiveModelIso (J : CochainComplex.Plus (InjectiveObject C)) {F : C}
    (e : DerivedCategory.Plus.Q.obj ((InjectiveObject.ι C).mapCochainComplexPlus.obj J) ≅
      (DerivedCategory.Plus.singleFunctor C 0).obj F) :
    DerivedCategory.Plus.Q.obj ((InjectiveObject.ι C').mapCochainComplexPlus.obj
        ((restrictInjectiveObject r).mapCochainComplexPlus.obj J)) ≅
      (DerivedCategory.Plus.singleFunctor C' 0).obj (r.obj F) :=
  DerivedCategory.Plus.ι.preimageIso
    ((r.mapDerivedCategoryFactors.app
        (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj)).symm ≪≫
      r.mapDerivedCategory.mapIso (DerivedCategory.Plus.ι.mapIso e ≪≫
        (DerivedCategory.Plus.singleFunctorιIso C 0).app F) ≪≫
      (r.mapDerivedCategorySingleFunctor 0).app F ≪≫
      ((DerivedCategory.Plus.singleFunctorιIso C' 0).app (r.obj F)).symm)

/-- **The right derived functor of `G` at `r(F)` is computed on `r` of an injective model of `F`**,
for `r` exact and preserving injective objects. -/
def qIsoRightDerivedFunctorPlusOfExact (G : C' ⥤ D) [G.Additive]
    (J : CochainComplex.Plus (InjectiveObject C)) {F : C}
    (e : DerivedCategory.Plus.Q.obj ((InjectiveObject.ι C).mapCochainComplexPlus.obj J) ≅
      (DerivedCategory.Plus.singleFunctor C 0).obj F) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((r.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj J.obj))) ≅
      DerivedCategory.Plus.ι.obj (G.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor C' 0).obj (r.obj F))) :=
  qIsoRightDerivedFunctorPlus G ((restrictInjectiveObject r).mapCochainComplexPlus.obj J)
    (restrictInjectiveModelIso r J e)

end Derived

section Biprod

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasBinaryBiproducts D]
  (Φ Ψ : C ⥤ D) [Φ.Additive] [Ψ.Additive]

/-- **A biproduct of two functors, evaluated at an object, is the biproduct of the values.** -/
def biprodObjIso (X : C) : (Φ ⊞ Ψ).obj X ≅ Φ.obj X ⊞ Ψ.obj X where
  hom := biprod.lift ((biprod.fst : Φ ⊞ Ψ ⟶ Φ).app X) ((biprod.snd : Φ ⊞ Ψ ⟶ Ψ).app X)
  inv := biprod.desc ((biprod.inl : Φ ⟶ Φ ⊞ Ψ).app X) ((biprod.inr : Ψ ⟶ Φ ⊞ Ψ).app X)
  hom_inv_id := by
    rw [biprod.lift_desc, ← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.app_add,
      biprod.total, NatTrans.id_app]
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
        biprod.lift_fst, biprod.lift_snd, Category.comp_id,
        ← NatTrans.comp_app, biprod.inl_fst, biprod.inl_snd, biprod.inr_fst, biprod.inr_snd,
        NatTrans.id_app, NatTrans.app_zero]

/-- **A biproduct of two additive functors applied to a complex is the biproduct of the two
complexes.**  The comparison is the pair of projections, applied degreewise. -/
def mapHomologicalComplexBiprodIso [(Φ ⊞ Ψ).Additive] {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex C c) :
    ((Φ ⊞ Ψ).mapHomologicalComplex c).obj K ≅
      (Φ.mapHomologicalComplex c).obj K ⊞ (Ψ.mapHomologicalComplex c).obj K := by
  let A := (NatTrans.mapHomologicalComplex (biprod.fst : Φ ⊞ Ψ ⟶ Φ) c).app K
  let B := (NatTrans.mapHomologicalComplex (biprod.snd : Φ ⊞ Ψ ⟶ Ψ) c).app K
  let C' := (NatTrans.mapHomologicalComplex (biprod.inl : Φ ⟶ Φ ⊞ Ψ) c).app K
  let D' := (NatTrans.mapHomologicalComplex (biprod.inr : Ψ ⟶ Φ ⊞ Ψ) c).app K
  have hCA : C' ≫ A = 𝟙 _ := by
    ext i
    rw [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f, ← NatTrans.comp_app,
      biprod.inl_fst, NatTrans.id_app]
    rfl
  have hCB : C' ≫ B = 0 := by
    ext i
    rw [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f, ← NatTrans.comp_app,
      biprod.inl_snd, NatTrans.app_zero]
  have hDA : D' ≫ A = 0 := by
    ext i
    rw [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.zero_f, ← NatTrans.comp_app,
      biprod.inr_fst, NatTrans.app_zero]
  have hDB : D' ≫ B = 𝟙 _ := by
    ext i
    rw [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f, ← NatTrans.comp_app,
      biprod.inr_snd, NatTrans.id_app]
    rfl
  have hAC : A ≫ C' + B ≫ D' = 𝟙 _ := by
    ext i
    rw [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
      NatTrans.mapHomologicalComplex_app_f, NatTrans.mapHomologicalComplex_app_f,
      NatTrans.mapHomologicalComplex_app_f, NatTrans.mapHomologicalComplex_app_f,
      HomologicalComplex.id_f, ← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.app_add,
      biprod.total, NatTrans.id_app]
    rfl
  exact
    { hom := biprod.lift A B
      inv := biprod.desc C' D'
      hom_inv_id := by rw [biprod.lift_desc, hAC]
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [hCA, hCB, hDA, hDB] }

end Biprod

end Stacks.RightDerivedPlusTriangle

end
