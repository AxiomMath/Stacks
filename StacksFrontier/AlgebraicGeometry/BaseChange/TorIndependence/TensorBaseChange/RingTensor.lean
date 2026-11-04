module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.ModelTensor
public import StacksFrontier.Algebra.Homology.LocalizedModuleHomology

/-!
# The map of Stacks 0DJ7 for a tensor product with a K-flat complex, over rings

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a square of rings in which `A'` is a localization of
`A ⊗_R R'`.  Let `N` be a complex of `A`-modules with a map `A' ⊗_A N ⟶ Z` whose map of
Stacks 0DJ7 is an isomorphism in every degree.  For a K-flat complex `P` of `A`-modules the map of
Stacks 0DJ7 at `A' ⊗_A (P ⊗_A N) ≅ (A' ⊗_A P) ⊗_{A'} (A' ⊗_A N) ⟶ (A' ⊗_A P) ⊗_{A'} Z` is then an
isomorphism in every degree.  This is the ring-level computation of the source and the target of
the map of Stacks 0DJ7 by transitivity of the derived tensor product (Tag 0BYJ).

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_tensor`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct ChangeOfRings
open CochainComplex.DerivedExtensionScalars

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-- If isomorphisms `e : X ≅ Y` and `e' : X' ≅ Y'` intertwine `a : X ⟶ X'` and `b : Y ⟶ Y'`,
then their inverses intertwine `b` and `a`. -/
theorem Iso.inv_naturality_of_hom {C : Type*} [Category C] {X Y X' Y' : C} {e : X ≅ Y}
    {e' : X' ≅ Y'} {a : X ⟶ X'} {b : Y ⟶ Y'} (h : a ≫ e'.hom = e.hom ≫ b) :
    b ≫ e'.inv = e.inv ≫ a := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem ModuleCat.isLocalizedModule_iff_of_comm {R : Type u} [CommRing R] (S : Submonoid R)
    {X Y X' Y' : ModuleCat.{u} R} (a : X ⟶ Y) (b : X' ⟶ Y') (e₁ : X ≅ X') (e₂ : Y ≅ Y')
    (h : a ≫ e₂.hom = e₁.hom ≫ b) :
    IsLocalizedModule S a.hom ↔ IsLocalizedModule S b.hom := by
  rw [← IsLocalizedModule.comp_iff_of_bijective_left (S := S) (f := a.hom) e₂.hom.hom
      e₂.toLinearEquiv.bijective,
    ← IsLocalizedModule.comp_iff_of_bijective_right (S := S) (f := b.hom) e₁.hom.hom
      e₁.toLinearEquiv.bijective, ← ModuleCat.hom_comp, h, ModuleCat.hom_comp]

/-- For a morphism `f` of cochain complexes of `R`-modules, the map induced by `f` on the `n`-th
cohomology in the derived category is a localization at `S` if and only if the map
`HomologicalComplex.homologyMap f n` is. -/
theorem isLocalizedModule_homologyFunctor_map_Q_iff {R : Type u} [CommRing R]
    (S : Submonoid R) {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) (n : ℤ) :
    IsLocalizedModule S
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map (DerivedCategory.Q.map f)).hom ↔
      IsLocalizedModule S (HomologicalComplex.homologyMap f n).hom :=
  ModuleCat.isLocalizedModule_iff_of_comm S _ _
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app X)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app Y)
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).hom.naturality f)

section TensorModel

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local notation "B₀" => A ⊗[R] R₀

/-- The inverse of `projectionIso X W` is natural in the `A'`-module `W`. -/
theorem projectionIso_inv_naturality_right (X : ModuleCat.{u} A) {W W' : ModuleCat.{u} A'}
    (g : W ⟶ W') :
    (baseChangeFunctor A B₀).obj X ◁ (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map g ≫
      (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W').inv =
    (projectionIso (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) X W).inv ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeFunctor A A').obj X ◁ g) :=
  Iso.inv_naturality_of_hom (projectionIso_naturality_right X g)

/-- The inverse of `projectionComplexIso' P Z` is natural in the complex `Z` of `A'`-modules. -/
theorem projectionComplexIso'_inv_naturality (P : CochainComplex (ModuleCat.{u} A) ℤ)
    {Z Z' : CochainComplex (ModuleCat.{u} A') ℤ} (v : Z ⟶ Z') :
    (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map v) ≫ (projectionComplexIso' P Z').inv =
      (projectionComplexIso' P Z).inv ≫
        ((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ v) := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.Monoidal.ι_whiskerLeft_assoc, ι_projectionComplexIso'_inv]
  have e := ι_projectionComplexIso'_inv (R := R) (R' := R') (A' := A') (R₀ := R₀) P Z p q n h
  refine Eq.trans ?_ (congrArg (fun t => t ≫ (((ModuleCat.restrictScalars
    (modelRingMap R A R' A' R₀)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ v)).f n)
        e).symm
  have e2 : (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) Z
          p q n h) ≫
      (((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ v)).f n =
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        ((baseChangeFunctor A A').obj (P.X p) ◁ v.f q) ≫
      (ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).map
        (HomologicalComplex.ιTensorObj
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P) Z'
          p q n h) := by
    rw [Functor.mapHomologicalComplex_map_f, ← Functor.map_comp, ← Functor.map_comp,
      HomologicalComplex.Monoidal.ι_whiskerLeft]
    rfl
  rw [Category.assoc, e2]
  exact ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ _)
    (projectionIso_inv_naturality_right (R := R) (R' := R') (R₀ := R₀) (P.X p) (v.f q)))).trans
      (Category.assoc _ _ _)

variable (F : CochainComplex (ModuleCat.{u} R₀) ℤ)
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))

/-- **The model of a tensor product, with a target.** -/
theorem modelKappa_tensor (P N : CochainComplex (ModuleCat.{u} A) ℤ)
    (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z) :
    ((bcComplexTensorIso A B₀ P N).inv ▷
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≫
      modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε (P ⊗ N)
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ Z)
        ((extTensorIso P N).hom ≫
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ α)) =
    (α_ _ _ _).hom ≫
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
        modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α) ≫
      (projectionComplexIso' P Z).inv := by
  have h1 := modelMapX_tensor (R := R) (A' := A') F ε P N
  have h2 := projectionComplexIso'_inv_naturality (R := R) (R' := R') (A' := A') (R₀ := R₀) P α
  dsimp only [modelKappa]
  rw [Functor.map_comp, MonoidalCategory.whiskerLeft_comp, reassoc_of% h1, Category.assoc, h2]

end TensorModel

end RingTheory.TorIndependence

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard Algebra.TensorProduct.rightAlgebra

section TensorCriterion

variable {R A R' A' R₀ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₀]
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R R₀] [Algebra R₀ R'] [IsScalarTower R R₀ R']

local notation "B₀" => A ⊗[R] R₀

variable {F : CochainComplex (ModuleCat.{u} R₀) ℤ}
  (ε : F ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R₀) 0).obj (ModuleCat.of R₀ R'))
  [Module.Flat R R₀] (hF : F.KFlat) [QuasiIso ε]

include ε hF in
/-- **The base-change map of Stacks 0DJ7 for a tensor product with a K-flat complex**, in the
model. -/
theorem isIso_ringBaseChangeCohomologyMap_tensor_of_model
    (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (hsurj : Function.Surjective (algebraMap R₀ R'))
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (h : ∀ n, IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n)) (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj (P ⊗ N))
      (DerivedCategory.Q.obj
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ Z))
      (alphaH A A' (P ⊗ N) ≫ DerivedCategory.Q.map ((extTensorIso P N).hom ≫
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ α))) n) := by
  rw [isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule ε hF n S hloc hsurj,
    isLocalizedModule_homologyFunctor_map_Q_iff]
  have hN : ∀ m, IsLocalizedModule (S.comap (modelBaseRingMap R A R' R₀))
      (HomologicalComplex.homologyMap
        (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α) m).hom :=
    fun m => (isLocalizedModule_homologyFunctor_map_Q_iff _ _ m).1
      ((isIso_ringBaseChangeCohomologyMap_iff_isLocalizedModule ε hF m S hloc hsurj N Z α).1 (h m))
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  have hZ : ∀ i (s : S.comap (modelBaseRingMap R A R' R₀)),
      IsUnit (algebraMap B₀ (Module.End B₀
        ((((ModuleCat.restrictScalars (modelRingMap R A R' A' R₀)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj Z).X i)) s) := by
    intro i s
    have hu : IsUnit (modelRingMap R A R' A' R₀ s) := IsLocalization.map_units A' (⟨_, s.2⟩ : S)
    rw [Module.End.isUnit_iff]
    exact IsUnit.smul_bijective (β := Z.X i) hu
  have hL := CochainComplex.isLocalizedModule_homologyMap_whiskerLeft
    (S.comap (modelBaseRingMap R A R' R₀))
    (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
    (kFlat_baseChangeFunctor_obj A B₀ hP)
    (modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α) hZ hN n
  have key := modelKappa_tensor (R := R) (A' := A') F ε P N Z α
  have hκ : modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε (P ⊗ N)
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ Z)
        ((extTensorIso P N).hom ≫
          (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ α)) ≫
        (projectionComplexIso' P Z).hom =
      (((bcComplexTensorIso A B₀ P N).hom ▷
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≫
        (α_ _ _ _).hom) ≫
      (((baseChangeFunctor A B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁
        modelKappa (R := R) (A := A) (R' := R') (A' := A') (R₀ := R₀) ε N Z α) := by
    rw [← cancel_epi ((bcComplexTensorIso A B₀ P N).inv ▷
        ((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F)]
    dsimp only [modelKappa] at key ⊢
    rw [Category.assoc (modelMapX ε (P ⊗ N)), reassoc_of% key, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  refine (ModuleCat.isLocalizedModule_iff_of_comm _ _ _
    (HomologicalComplex.homologyMapIso (whiskerRightIso (bcComplexTensorIso A B₀ P N)
      (((baseChangeFunctor R₀ B₀).mapHomologicalComplex (ComplexShape.up ℤ)).obj F) ≪≫
        α_ _ _ _) n)
    (HomologicalComplex.homologyMapIso (projectionComplexIso' P Z) n) ?_).2 hL
  rw [HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hκ]
  rfl

end TensorCriterion

end RingTheory.TorIndependence

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

section TensorUnconditional

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- **The base-change map of Stacks 0DJ7 for a tensor product with a K-flat complex.** Let
`A'` be a localization of `A ⊗_R R'`. If the base-change map at `(N, Z, α)` is invertible in
every degree, so is the one at `(P ⊗_A N, (A' ⊗_A P) ⊗_{A'} Z, A' ⊗_A P ⊗ α)` for every K-flat
complex `P` of `A`-modules. -/
theorem isIso_ringBaseChangeCohomologyMap_tensor
    (S : Submonoid (A ⊗[R] R'))
    (hloc : letI := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
      IsLocalization S A')
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat)
    (N : CochainComplex (ModuleCat.{u} A) ℤ) (Z : CochainComplex (ModuleCat.{u} A') ℤ)
    (α : ((ModuleCat.extendScalars (algebraMap A A')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ Z)
    (h : ∀ n, IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj N)
        (DerivedCategory.Q.obj Z) (alphaH A A' N ≫ DerivedCategory.Q.map α) n)) (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') (DerivedCategory.Q.obj (P ⊗ N))
      (DerivedCategory.Q.obj
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⊗ Z))
      (alphaH A A' (P ⊗ N) ≫ DerivedCategory.Q.map ((extTensorIso P N).hom ≫
        (((baseChangeFunctor A A').mapHomologicalComplex (ComplexShape.up ℤ)).obj P ◁ α))) n) := by
  let : Algebra (MvPolynomial R' R) R' :=
    (MvPolynomial.aeval (R := R) (fun x : R' => x)).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial R' R) R' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      ((MvPolynomial.aeval (R := R) (fun x : R' => x)).commutes r).symm
  have hsurj : Function.Surjective (algebraMap (MvPolynomial R' R) R') := fun x =>
    ⟨MvPolynomial.X x, MvPolynomial.aeval_X _ x⟩
  obtain ⟨F, ε, hF, -, hε, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u}
    ((CochainComplex.singleFunctor (ModuleCat.{u} (MvPolynomial R' R)) 0).obj
      (ModuleCat.of (MvPolynomial R' R) R'))
  exact isIso_ringBaseChangeCohomologyMap_tensor_of_model (R₀ := MvPolynomial R' R) ε hF S hloc
    hsurj P hP N Z α h n

end TensorUnconditional

end RingTheory.TorIndependence
