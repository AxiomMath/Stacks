module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtTensorPullbackPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexSingle
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Algebra.Homology.TotalSingleRowNaturality

/-!
# `Ext^i(ℱ[0], 𝒢[0] ⊗ f^*𝒩)` for modules `ℱ`, `𝒢`, `𝒩`

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `ℱ`, `𝒢` modules on `X` and `𝒩` a module on
`Y`.  The complex `𝒢[0] ⊗ f^*𝒩[0]` (`AlgebraicGeometry.Space.tensorPullbackComplex`) is the
module `𝒢 ⊗ f^*𝒩` placed in degree zero.  Hence

* `Ext^0(ℱ[0], 𝒢[0] ⊗ f^*𝒩) = Hom(ℱ, 𝒢 ⊗ f^*𝒩)`, naturally in `𝒩`
  (`AlgebraicGeometry.Space.tensorPullbackExtGroupSingleZeroEquiv`);
* `Ext^i(ℱ[0], 𝒢[0] ⊗ f^*𝒩) = 0` for `i < 0`
  (`AlgebraicGeometry.Space.subsingleton_tensorPullbackExtGroup_single_of_neg`).

These are the forms in which Stacks 08JR (A), at `E = ℱ[0]` and `𝒢^• = 𝒢[0]`, enters the proof
of Stacks 08JY.

## Implementation notes

A step of the proof of Stacks 08K6; no declaration here carries a `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D] [Abelian A] [Abelian B]
  [Abelian D] (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]

/-- The termwise complex of a complex concentrated in degree zero is concentrated in degree
zero. -/
def rowComplexSingleObjIso (K₀ : A) (M : B) :
    rowComplex F ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj K₀) M ≅
      (HomologicalComplex.single D (ComplexShape.up ℤ) 0).obj ((F.obj K₀).obj M) where
  hom := HomologicalComplex.mkHomToSingle
    ((F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 K₀).hom).app M)
    (fun i hi ↦ (isZero_obj_obj_of_isZero F (HomologicalComplex.isZero_single_obj_X _ _ _ i (by
      change i + 1 = 0 at hi; omega)) M).eq_of_src _ _)
  inv := HomologicalComplex.mkHomFromSingle
    ((F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 K₀).inv).app M)
    (fun k hk ↦ (isZero_obj_obj_of_isZero F (HomologicalComplex.isZero_single_obj_X _ _ _ k (by
      change 0 + 1 = k at hk; omega)) M).eq_of_tgt _ _)
  hom_inv_id := HomologicalComplex.hom_ext _ _ fun n ↦ by
    by_cases hn : n = 0
    · subst hn
      simp [HomologicalComplex.mkHomToSingle, HomologicalComplex.mkHomFromSingle, rowComplex,
        ← NatTrans.comp_app, ← F.map_comp]
    · exact (isZero_obj_obj_of_isZero F
        (HomologicalComplex.isZero_single_obj_X _ _ _ n hn) M).eq_of_src _ _
  inv_hom_id := HomologicalComplex.from_single_hom_ext (by
    simp [HomologicalComplex.mkHomToSingle, HomologicalComplex.mkHomFromSingle, rowComplex,
      ← NatTrans.comp_app_assoc, ← F.map_comp])

omit [Abelian B] [∀ X, (F.obj X).Additive] in
/-- The identification of the termwise complex of a complex concentrated in degree zero is
natural in the second variable. -/
@[reassoc]
theorem rowComplexSingleObjIso_hom_naturality (K₀ : A) {M M' : B} (g : M ⟶ M') :
    rowComplexMapRight F _ g ≫ (rowComplexSingleObjIso F K₀ M').hom =
      (rowComplexSingleObjIso F K₀ M).hom ≫
        (HomologicalComplex.single D (ComplexShape.up ℤ) 0).map ((F.obj K₀).map g) :=
  HomologicalComplex.to_single_hom_ext (by
    have h₁ : ∀ X : D, HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X 0 rfl =
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X := fun _ ↦ rfl
    simp only [rowComplexSingleObjIso, HomologicalComplex.mkHomToSingle, rowComplexMapRight,
      rowComplex, HomologicalComplex.single_map_f_self, HomologicalComplex.comp_f, ↓reduceDIte,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp, h₁, Iso.inv_hom_id_assoc,
      Category.assoc]
    exact NatTrans.naturality_assoc _ g _)

end CochainComplex.KFlatBifunctor

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}
  (f : X ⟶ Y) (G : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))

/-- **`𝒢[0] ⊗ f^*𝒩[0] ≅ (𝒢 ⊗ f^*𝒩)[0]`.** -/
def tensorPullbackComplexSingleSingleIso
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (tensorPullbackComplex f ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N) ≅
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (((tensorPullbackBifunctor f).obj G).obj N) :=
  CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) _ N ≪≫
    CochainComplex.KFlatBifunctor.rowComplexSingleObjIso (tensorPullbackBifunctor f) G N

/-- **The identification `𝒢[0] ⊗ f^*𝒩[0] ≅ (𝒢 ⊗ f^*𝒩)[0]` is natural in `𝒩`.** -/
theorem tensorPullbackComplexSingleSingleIso_hom_naturality
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : N ⟶ N') :
    (tensorPullbackComplex f ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q) ≫
        (tensorPullbackComplexSingleSingleIso f G N').hom =
      (tensorPullbackComplexSingleSingleIso f G N).hom ≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (((tensorPullbackBifunctor f).obj G).map q) := by
  show HomologicalComplex.mapBifunctorMap
      (𝟙 ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q) (tensorPullbackBifunctor f)
      (ComplexShape.up ℤ) ≫
      ((CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) _ N').hom ≫
        (CochainComplex.KFlatBifunctor.rowComplexSingleObjIso
          (tensorPullbackBifunctor f) G N').hom) =
    ((CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) _ N).hom ≫
        (CochainComplex.KFlatBifunctor.rowComplexSingleObjIso
          (tensorPullbackBifunctor f) G N).hom) ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        (((tensorPullbackBifunctor f).obj G).map q)
  rw [reassoc_of% (CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality_right
    (tensorPullbackBifunctor f) _ q),
    CochainComplex.KFlatBifunctor.rowComplexSingleObjIso_hom_naturality, Category.assoc]

variable (F : Modules.{u, u} B S hS X.1 X.2)

/-- The identification `(𝒢[0] ⊗ f^*𝒩[0])[0] ≅ (𝒢 ⊗ f^*𝒩)[0]` in the derived category. -/
def tensorPullbackComplexDerivedSingleShiftZeroIso
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (tensorPullbackComplexDerived f ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N))⟦(0 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj
        (((tensorPullbackBifunctor f).obj G).obj N) :=
  (shiftFunctorZero (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) ℤ).app _ ≪≫
    DerivedCategory.Q.mapIso (tensorPullbackComplexSingleSingleIso f G N)

/-- **`Ext^0(ℱ[0], 𝒢[0] ⊗ f^*𝒩) = Hom(ℱ, 𝒢 ⊗ f^*𝒩)`.** -/
def tensorPullbackExtGroupSingleZeroEquiv
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (tensorPullbackExtGroup B S hS
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) N 0 : Type (u + 1)) ≃
      (F ⟶ ((tensorPullbackBifunctor f).obj G).obj N) where
  toFun x := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).preimage
    (x ≫ (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).hom)
  invFun φ := (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ ≫
    (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).inv
  left_inv x :=
    (congrArg (· ≫ (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).inv)
      (Functor.map_preimage (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0)
        (x ≫ (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).hom))).trans
      ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·)
        (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).hom_inv_id).trans
        (Category.comp_id x)))
  right_inv φ :=
    (congrArg (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).preimage
      ((Category.assoc _ _ _).trans ((congrArg
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map φ ≫ ·)
        (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).inv_hom_id).trans
        (Category.comp_id _)))).trans
      (Functor.preimage_map
        (F := DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0) φ)

/-- The identification `(𝒢[0] ⊗ f^*𝒩[0])[0] ≅ (𝒢 ⊗ f^*𝒩)[0]` is natural in `𝒩`. -/
theorem tensorPullbackComplexDerivedSingleShiftZeroIso_hom_naturality
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : N ⟶ N') :
    ((DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map ((tensorPullbackComplex f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q)))⟦(0 : ℤ)⟧' ≫
        (tensorPullbackComplexDerivedSingleShiftZeroIso f G N').hom =
      (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).hom ≫
        (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).map
          (((tensorPullbackBifunctor f).obj G).map q) := by
  have h₁ := (shiftFunctorZero (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) ℤ).hom.naturality
    ((DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map ((tensorPullbackComplex f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q)))
  have h₂ :=
    (Functor.map_comp (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)) _ _).symm.trans
      ((congrArg (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map
        (tensorPullbackComplexSingleSingleIso_hom_naturality f G q)).trans
        (Functor.map_comp (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)) _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

/-- **`Ext^0(ℱ[0], 𝒢[0] ⊗ f^*𝒩) = Hom(ℱ, 𝒢 ⊗ f^*𝒩)` is natural in `𝒩`.** -/
theorem tensorPullbackExtGroupSingleZeroEquiv_naturality
    {N N' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : N ⟶ N')
    (x : (tensorPullbackExtGroup B S hS
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) N 0 : Type (u + 1))) :
    tensorPullbackExtGroupSingleZeroEquiv f G F N'
        (tensorPullbackExtGroupMap B S hS
          ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) f
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) q 0 x) =
      tensorPullbackExtGroupSingleZeroEquiv f G F N x ≫
        ((tensorPullbackBifunctor f).obj G).map q := by
  show (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).preimage
      ((x ≫ ((DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).map ((tensorPullbackComplex f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)).map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map q)))⟦(0 : ℤ)⟧') ≫
        (tensorPullbackComplexDerivedSingleShiftZeroIso f G N').hom) =
    (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).preimage
      (x ≫ (tensorPullbackComplexDerivedSingleShiftZeroIso f G N).hom) ≫
        ((tensorPullbackBifunctor f).obj G).map q
  exact (congrArg (DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).preimage
    ((Category.assoc _ _ _).trans ((congrArg (x ≫ ·)
      (tensorPullbackComplexDerivedSingleShiftZeroIso_hom_naturality f G q)).trans
      (Category.assoc _ _ _).symm))).trans
    ((Functor.preimage_comp _ _).trans (congrArg (_ ≫ ·) (Functor.preimage_map
      (F := DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0) _)))

/-- **`Ext^i(ℱ[0], 𝒢[0] ⊗ f^*𝒩) = 0` for `i < 0`.** -/
theorem subsingleton_tensorPullbackExtGroup_single_of_neg
    (N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) {i : ℤ} (hi : i < 0) :
    Subsingleton (tensorPullbackExtGroup B S hS
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) N i : Type (u + 1)) := by
  let M : Modules.{u, u} B S hS X.1 X.2 := ((tensorPullbackBifunctor f).obj G).obj N
  let K : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ :=
    ((CochainComplex.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj M)⟦i⟧
  have : K.IsStrictlyGE (-i) :=
    CochainComplex.isStrictlyGE_shift _ 0 i (-i) (by omega)
  have hsub : Subsingleton
      ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F ⟶
        (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).obj K) :=
    DerivedCategory.subsingleton_hom_of_isStrictlyLE_of_isStrictlyGE
      ((CochainComplex.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F) K 0 (-i) (by omega)
  let e : (tensorPullbackComplexDerived f
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N))⟦i⟧ ≅
      (DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).obj K :=
    (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) i).mapIso
        ((DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).mapIso
          (tensorPullbackComplexSingleSingleIso f G N)) ≪≫
      ((DerivedCategory.Q (C := Modules.{u, u} B S hS X.1 X.2)).commShiftIso i).symm.app _
  exact (Iso.homCongr (Iso.refl _) e).subsingleton

end AlgebraicGeometry.Space

end
