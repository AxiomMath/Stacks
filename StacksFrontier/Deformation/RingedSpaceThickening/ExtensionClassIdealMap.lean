module

public import StacksFrontier.Algebra.Homology.DoubleMappingCone
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionFromPushout
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledIdealConormal
public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAlgebraExtensionBridge

/-!
# The class of a square-zero extension restricted to the ideal of the base thickening

Let `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` and `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be morphisms of ringed spaces,
`𝒥 = Ker(t^♯)` the ideal sheaf of `t`, and `𝒢` an `𝒪_X`-module. A square-zero extension
`0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `(f ∘ t)⁻¹𝒪_{S'}`-algebras carries a section of `𝒥` into the
square-zero ideal, so it induces a map `f^* t^* 𝒥 ⟶ 𝒢`: the *ideal map* of the extension, which
for the extension attached to a solution of the deformation problem of **Stacks 08U7** is the
prescribed map `c`. This file proves that the ideal map is what the class of the extension in
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S'}, 𝒢)` restricts to along the map `(f^* t^* 𝒥)[1] ⟶ 𝖭𝖫_{X/S'}` sending a
section of `𝒥` to the conormal class of its image in `(f ∘ t)⁻¹𝒪_{S'}[𝒪_X]`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.idealMap`: the ideal map
  `f^* t^* 𝒥 ⟶ 𝒢` of an extension.
* `AlgebraicGeometry.RingedSpaceThickening.idealConormalMap`: the map `f^* t^* 𝒥 ⟶ 𝒥'/𝒥'²` into
  the degree `-1` term of `𝖭𝖫_{X/S'}`, and
  `AlgebraicGeometry.RingedSpaceThickening.idealToNaiveCotangent`: the induced map
  `(f^* t^* 𝒥)[1] ⟶ 𝖭𝖫_{X/S'}` in `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.idealMap_eq_iff`: the
  ideal map is `c` exactly when the extension induces `c` on sections of `𝒥`, and
  `AlgebraicGeometry.RingedSpaceThickening.DeformationSolution.toAlgebraExtension_idealMap`: the
  ideal map of the extension of a solution is the prescribed map.
* `AlgebraicGeometry.RingedSpaceThickening.idealConormalMap_comp_d`: the map into the conormal
  term is killed by the differential, the coefficients having zero differential.
* `AlgebraicGeometry.RingedSpaceThickening.idealToNaiveCotangent_comp_extClass`: **the class of
  an extension restricted along `(f^* t^* 𝒥)[1] ⟶ 𝖭𝖫_{X/S'}` is minus the shifted ideal map.**

## Implementation notes

The sign in `idealToNaiveCotangent_comp_extClass` is that of the triangle of a mapping cone in
Mathlib, whose third map is induced by `-fst`
(`CochainComplex.mappingCone.inl_v_triangle_mor₃_f`): for a chain map from a complex
concentrated in degree `-1` into a two-term complex `X₀ ⟶ X₁` with component `a`, the projection
onto `X₀[1]` is `-a[1]` (`CochainComplex.singleZeroShiftOneIso_hom_comp_doubleProjQ`).

Maps out of `f^* t^* 𝒥` are handled through their transposes along `(f ∘ t)^* ⊣ (f ∘ t)_*`
(`AlgebraicGeometry.RingedSpaceThickening.prescribedIdealMap`), which are maps of
`𝒪_{S'}`-modules out of `𝒥` and are compared on sections.

The map into the conormal term of a presentation is the ideal map of the square-zero pushout of
the presentation along the identity of its conormal sheaf
(`AlgebraicGeometry.RingedSpaceThickening.extensionOfConormalHom`), so that its linearity is
that of an ideal map.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Sites.Conormal (IdealRestriction kernelIdeal presentationScalar)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafCoefficientMap_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe w v u z

/-! ### The projection of a two-term complex on a complex concentrated in degree `-1` -/

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A chain map into a two-term complex from a complex concentrated in degree `-1`, followed by
the third map of the triangle of the cone on the differential.** It is minus the shifted
degree `-1` component, read through the identification `(M[0])⟦1⟧ ≅ M[-1]`. -/
theorem mkHom_comp_triangle_mor₃ {M X₀ X₁ : C} (d : X₀ ⟶ X₁) (a : M ⟶ X₀)
    (ψ : (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M ⟶
      HomologicalComplex.double d ComplexShape.upIntRelNegOneZero)
    (hψ : ψ.f (-1) = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) M).hom ≫ a ≫
      (HomologicalComplex.doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv)
    (e : ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)⟦(1 : ℤ)⟧ ≅
      (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M)
    (he : e = ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app M)
    (m₃ : mappingCone ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d) ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₀)⟦(1 : ℤ)⟧)
    (hm₃ : m₃ =
      (mappingCone.triangle ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d)).mor₃) :
    ψ ≫ doubleToMappingCone d ComplexShape.upIntRelNegOneZero ≫ m₃ =
      -(e.inv ≫ ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a)⟦(1 : ℤ)⟧') := by
  subst he
  refine HomologicalComplex.from_single_hom_ext ?_
  have hinl : (mappingCone.inl ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d)).v 0
      (-1) (by norm_num) ≫ m₃.f (-1) =
      -(shiftFunctorObjXIso ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₀) 1 (-1) 0
        (by norm_num)).inv := by
    rw [hm₃]
    exact mappingCone.inl_v_triangle_mor₃_f _ 0 (-1) (by norm_num)
  have h₀ : (doubleToMappingCone d ComplexShape.upIntRelNegOneZero).f (-1) =
      (HomologicalComplex.doubleXIso₀ d ComplexShape.upIntRelNegOneZero).hom ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X₀).inv ≫
          (mappingCone.inl ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d)).v 0 (-1)
            (by norm_num) :=
    HomologicalComplex.mkHomFromDouble_f₀ _ _ _ _ _ _
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, hψ, h₀]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, hinl]
  simp [HomologicalComplex.single_map_f_self, CochainComplex.singleFunctors,
    shiftFunctorObjXIso, HomologicalComplex.singleObjXSelf, HomologicalComplex.XIsoOfEq,
    HomologicalComplex.singleObjXIsoOfEq]

/-- The chain map from a complex concentrated in degree `-1` into the two-term complex
`HomologicalComplex.double d` with `d` in degrees `-1` and `0`, given by a map `a` into the degree
`-1` term killed by `d`. -/
def singleNegOneToDouble {A X₀ X₁ : C} (d : X₀ ⟶ X₁) (a : A ⟶ X₀) (ha : a ≫ d = 0) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj A ⟶
      HomologicalComplex.double d ComplexShape.upIntRelNegOneZero :=
  HomologicalComplex.mkHomFromSingle (a ≫ (HomologicalComplex.doubleXIso₀ d _).inv)
    (fun k hk => by
      have hk' : k = 0 := by
        have h : (-1 : ℤ) + 1 = k := hk
        omega
      subst hk'
      rw [HomologicalComplex.double_d _ _ (by decide), Category.assoc, Iso.inv_hom_id_assoc,
        reassoc_of% ha, zero_comp])

/-- The degree `-1` component of `singleNegOneToDouble d a ha` is `a`, up to the identifications
of the degree `-1` terms of the two complexes. -/
theorem singleNegOneToDouble_f {A X₀ X₁ : C} (d : X₀ ⟶ X₁) (a : A ⟶ X₀) (ha : a ≫ d = 0) :
    (singleNegOneToDouble d a ha).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) A).hom ≫ a ≫
        (HomologicalComplex.doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- The chain map `singleNegOneToDouble d a ha` depends only on the map `a`. -/
theorem singleNegOneToDouble_congr {A X₀ X₁ : C} (d : X₀ ⟶ X₁) {a a' : A ⟶ X₀} (ha : a ≫ d = 0)
    (ha' : a' ≫ d = 0) (h : a = a') :
    singleNegOneToDouble d a ha = singleNegOneToDouble d a' ha' := by
  subst h
  rfl

/-- `singleNegOneToDouble` is natural in the two-term complex. -/
theorem singleNegOneToDouble_comp {A X₀ X₁ Y₀ Y₁ : C} (d : X₀ ⟶ X₁) (d' : Y₀ ⟶ Y₁) (a : A ⟶ X₀)
    (ha : a ≫ d = 0)
    (φ : HomologicalComplex.double d ComplexShape.upIntRelNegOneZero ⟶
      HomologicalComplex.double d' ComplexShape.upIntRelNegOneZero) (p : X₀ ⟶ Y₀)
    (hφ : φ.f (-1) = (HomologicalComplex.doubleXIso₀ d ComplexShape.upIntRelNegOneZero).hom ≫ p ≫
      (HomologicalComplex.doubleXIso₀ d' ComplexShape.upIntRelNegOneZero).inv)
    (ha' : (a ≫ p) ≫ d' = 0) :
    singleNegOneToDouble d a ha ≫ φ = singleNegOneToDouble d' (a ≫ p) ha' :=
  HomologicalComplex.from_single_hom_ext (by
    rw [HomologicalComplex.comp_f, singleNegOneToDouble_f, singleNegOneToDouble_f, hφ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

variable [HasDerivedCategory.{w} C]

/-- The identification `(M[0])⟦1⟧ ≅ M[-1]` in the derived category, with `M[-1]` the image of
the complex concentrated in degree `-1`. -/
def singleZeroShiftOneIso (M : C) :
    ((DerivedCategory.singleFunctor C 0).obj M)⟦(1 : ℤ)⟧ ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M) :=
  ((DerivedCategory.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app M ≪≫
    (DerivedCategory.singleFunctorIsoCompQ C (-1)).app M

/-- `singleZeroShiftOneIso` is the commutation of `Q` with the shift followed by the image under
`Q` of the identification `(M[0])⟦1⟧ ≅ M[-1]` of cochain complexes. -/
theorem singleZeroShiftOneIso_hom (M : C)
    (e : ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)⟦(1 : ℤ)⟧ ≅
      (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M)
    (he : e = ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app M) :
    (singleZeroShiftOneIso M).hom =
      (DerivedCategory.Q.commShiftIso (1 : ℤ)).inv.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map e.hom := by
  subst he
  simp only [Int.reduceNeg, DerivedCategory.Q_obj_single_obj, singleZeroShiftOneIso,
    DerivedCategory.singleFunctors, SingleFunctors.postcomp, Functor.comp_obj, NatIso.trans_app,
    DerivedCategory.singleFunctorIsoCompQ, Iso.trans_assoc, Iso.trans_hom, Iso.app_hom,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  exact (Category.id_comp _).trans (congrArg _ (Category.comp_id _))

/-- **The projection of a two-term complex onto its shifted degree `-1` term, restricted to a
complex concentrated in degree `-1`.** For a chain map `ψ : M[-1] ⟶ (X₀ ⟶ X₁)` with degree `-1`
component `a`, the composite `(M[0])⟦1⟧ ≅ M[-1] ⟶ (X₀ ⟶ X₁) ⟶ (X₀[0])⟦1⟧` is `-a⟦1⟧`; the sign
is that of the triangle of a mapping cone. -/
theorem singleZeroShiftOneIso_hom_comp_doubleProjQ {M X₀ X₁ : C} (d : X₀ ⟶ X₁) (a : M ⟶ X₀)
    (ψ : (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M ⟶
      HomologicalComplex.double d ComplexShape.upIntRelNegOneZero)
    (hψ : ψ.f (-1) = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) M).hom ≫ a ≫
      (HomologicalComplex.doubleXIso₀ d ComplexShape.upIntRelNegOneZero).inv) :
    (singleZeroShiftOneIso M).hom ≫ DerivedCategory.Q.map ψ ≫
        doubleProjQ d ComplexShape.upIntRelNegOneZero =
      -((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' := by
  obtain ⟨e, he⟩ : ∃ e : ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M)⟦(1 : ℤ)⟧ ≅
      (HomologicalComplex.single C (ComplexShape.up ℤ) (-1)).obj M,
      e = ((CochainComplex.singleFunctors C).shiftIso 1 (-1) 0 (by norm_num)).app M := ⟨_, rfl⟩
  obtain ⟨m₃, hm₃⟩ : ∃ m₃ : mappingCone
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d) ⟶
      ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₀)⟦(1 : ℤ)⟧,
      m₃ = (mappingCone.triangle
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map d)).mor₃ :=
    ⟨_, rfl⟩
  let cs := DerivedCategory.Q.commShiftIso (C := CochainComplex C ℤ) (1 : ℤ)
  have hcomp : e.hom ≫ ψ ≫ doubleToMappingCone d ComplexShape.upIntRelNegOneZero ≫ m₃ =
      -(((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a)⟦(1 : ℤ)⟧') :=
    (congrArg (e.hom ≫ ·) (mkHom_comp_triangle_mor₃ d a ψ hψ e he m₃ hm₃)).trans
      ((Preadditive.comp_neg _ _).trans (congrArg Neg.neg (e.hom_inv_id_assoc _)))
  have hQ : DerivedCategory.Q.map e.hom ≫ DerivedCategory.Q.map ψ ≫
      DerivedCategory.Q.map (doubleToMappingCone d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map m₃ =
      -DerivedCategory.Q.map
        (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a)⟦(1 : ℤ)⟧') := by
    simpa only [Functor.map_comp, Functor.map_neg] using congrArg DerivedCategory.Q.map hcomp
  have hproj : doubleProjQ d ComplexShape.upIntRelNegOneZero =
      DerivedCategory.Q.map (doubleToMappingCone d ComplexShape.upIntRelNegOneZero) ≫
        DerivedCategory.Q.map m₃ ≫
          cs.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₀) := by
    rw [hm₃]
    rfl
  have hnat : DerivedCategory.Q.map
      (((HomologicalComplex.single C (ComplexShape.up ℤ) 0).map a)⟦(1 : ℤ)⟧') ≫
        cs.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj X₀) =
      cs.hom.app ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) ≫
        ((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' :=
    Functor.commShiftIso_hom_naturality _ _ _
  rw [singleZeroShiftOneIso_hom M e he, hproj]
  simp only [Category.assoc]
  rw [reassoc_of% hQ, Preadditive.neg_comp, Preadditive.comp_neg, hnat, Iso.inv_hom_id_app_assoc]

/-- `singleZeroShiftOneIso_hom_comp_doubleProjQ` for `singleNegOneToDouble`. -/
theorem singleZeroShiftOneIso_hom_comp_singleNegOneToDouble_comp_doubleProjQ {M X₀ X₁ : C}
    (d : X₀ ⟶ X₁) (a : M ⟶ X₀) (ha : a ≫ d = 0) :
    (singleZeroShiftOneIso M).hom ≫ DerivedCategory.Q.map (singleNegOneToDouble d a ha) ≫
        doubleProjQ d ComplexShape.upIntRelNegOneZero =
      -((DerivedCategory.singleFunctor C 0).map a)⟦(1 : ℤ)⟧' :=
  singleZeroShiftOneIso_hom_comp_doubleProjQ d a _ (singleNegOneToDouble_f d a ha)

end CochainComplex

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B) [Presheaf.IsLocallySurjective J φ.hom]
  (X : Cᵒᵖ)

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- **The conormal class of a coefficient lying in the kernel ideal is killed by
`ℐ/ℐ² ⟶ ℬ ⊗ Ω`**: the coefficients have zero differential. -/
theorem conormalSequence_f_conormalClass_coefficient (r : R.obj.obj X)
    (hr : (a.hom.app X).hom r ∈ kernelIdeal φ.hom X) :
    ((conormalSequence.{v, u, w, z} J R A B a φ).f.val.app X)
      (conormalClass.{v, u, w, z} J R A B a φ X ⟨_, hr⟩) = 0 :=
  (conormalSequence_f_class.{v, u, w, z} J R A B a φ X _).trans
    (tensorDifferential_coefficient.{v, u, w, z} J R A B a φ X r)

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **A factorisation of presentations carries the conormal class of a coefficient to the
conormal class of the same coefficient**, the factorisation fixing the coefficients. -/
theorem conormalSheafMapOfFac_conormalClass_coefficient (A₂ : Sheaf J CommRingCat.{w})
    (a₂ : R ⟶ A₂) (φ₂ : A₂ ⟶ B) [Presheaf.IsLocallySurjective J φ₂.hom] (ψ : A ⟶ A₂)
    (hψ : ψ ≫ φ₂ = φ) (ha : a ≫ ψ = a₂) (r : R.obj.obj X)
    (hr : (a.hom.app X).hom r ∈ kernelIdeal φ.hom X)
    (hr₂ : (a₂.hom.app X).hom r ∈ kernelIdeal φ₂.hom X) :
    ((conormalSheafMapOfFac.{v, u, w, z} J B A A₂ φ φ₂ ψ hψ).val.app X)
        (conormalClass.{v, u, w, z} J R A B a φ X ⟨_, hr⟩) =
      conormalClass.{v, u, w, z} J R A₂ B a₂ φ₂ X ⟨_, hr₂⟩ :=
  (conormalSheafMapOfFac_toAssociatedModule.{v, u, w, z} J B A A₂ φ φ₂ ψ hψ X _).trans
    (congrArg (toAssociatedModule.{v, u, w, z} J A₂ B φ₂ (conormalPresheaf φ₂.hom) X)
      (congrArg (kernelIdeal φ₂.hom X).toCotangent
        (Subtype.ext (congrArg (fun k : R ⟶ A₂ => (k.hom.app X).hom r) ha))))

end Stacks.Sites.Conormal

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A : Sheaf J CommRingCat.{w}) (E₁ E₂ : Functor Cᵒᵖ (Type w)) (h : E₁ ⟶ E₂)
  (B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)
  (α₁ : E₁ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  (α₂ : E₂ ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
  [Presheaf.IsLocallySurjective J (presentation J A B a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A B a E₂ α₂).hom] (hα : h ≫ α₂ = α₁)
  [HasSheafify J AddCommGrpCat.{max w u v z}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w u v z}]

/-- In degree `-1` the chain map of a morphism of presentations is the map of conormal sheaves,
read through the identifications `HomologicalComplex.doubleXIso₀` of the two-term complexes. -/
theorem presentationNaiveCotangentComplexMap_f_negOne_doubleXIso₀ :
    (presentationNaiveCotangentComplexMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα).f (-1) =
      (HomologicalComplex.doubleXIso₀
          (presentationConormalSequence.{v, u, w, z} J A B a E₁ α₁).f
          ComplexShape.upIntRelNegOneZero).hom ≫
        presentationConormalMap.{v, u, w, z} J A E₁ E₂ h B a α₁ α₂ hα ≫
        (HomologicalComplex.doubleXIso₀
          (presentationConormalSequence.{v, u, w, z} J A B a E₂ α₂).f
          ComplexShape.upIntRelNegOneZero).inv := by
  have e₀ : ∀ (E : Functor _ (Type _)) (α : E ⟶ Stacks.Sites.FreeAlgebra.underlyingPresheaf J B)
      [Presheaf.IsLocallySurjective J (presentation J A B a E α).hom],
      HomologicalComplex.doubleXIso₀ (presentationConormalSequence.{v, u, w, z} J A B a E α).f
        ComplexShape.upIntRelNegOneZero =
      eqToIso (presentationNaiveCotangentComplex_X_negOne.{v, u, w, z} J A B a E α) :=
    fun _ _ _ => rfl
  rw [presentationNaiveCotangentComplexMap_f_negOne.{v, u, w, z}, e₀, e₀]
  rfl

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {f : X ⟶ S} {t : S ⟶ S'}

/-- Reassociation used to read off a composite through two known factorisations. -/
private theorem comp_comp_comp_eq_neg {C : Type*} [Category C] [Preadditive C]
    {A B D D' E F : C} (σ : A ⟶ B) (q : B ⟶ D) (i : D ⟶ D') (q' : B ⟶ D') (p : D' ⟶ E)
    (s : E ⟶ F) (x : A ⟶ E) (h₁ : q ≫ i = q') (h₂ : σ ≫ q' ≫ p = -x) :
    (σ ≫ q) ≫ i ≫ p ≫ s = -(x ≫ s) := by
  rw [Category.assoc, ← Category.assoc q i, h₁, ← Category.assoc q' p s, ← Category.assoc σ, h₂,
    Preadditive.neg_comp]

/-! ### The adjoint of an algebra structure on sections -/

/-- The unit `𝒪_{S'} ⟶ g_* g⁻¹𝒪_{S'}` of `g⁻¹ ⊣ g_*` on sheaves of rings. -/
abbrev baseUnit (g : X ⟶ S') :
    S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj (inverseImageBaseRing g) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).unit.app S'.sheaf

/-- The adjoint `𝒪_{S'} ⟶ g_* ℛ` of a map `g⁻¹𝒪_{S'} ⟶ ℛ`, on sections: the map applied to the
image of the section under the unit. -/
theorem homEquiv_app_apply (g : X ⟶ S') {R : Sheaf (Opens.grothendieckTopology X.carrier)
    CommRingCat.{u}} (b : inverseImageBaseRing g ⟶ R) (V : (Opens S'.carrier)ᵒᵖ)
    (s : S'.presheaf.obj V) :
    (((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv _ _
        b).hom.app V).hom s =
      (b.hom.app (op ((Opens.map g.hom.base).obj V.unop))).hom (((baseUnit g).hom.app V).hom s) :=
  congrArg (fun k : S'.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} g.hom.base).obj R =>
    (k.hom.app V).hom s)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g.hom.base).homEquiv_unit
      S'.sheaf R b)

/-- The image under the unit of a section of `𝒪_{S'}` killed by `t^♯` is carried by any map
`(f ∘ t)⁻¹𝒪_{S'} ⟶ ℛ` over `𝒪_X` into the kernel of `ℛ ⟶ 𝒪_X`. -/
theorem baseUnit_mem_kernelIdeal {R : Sheaf (Opens.grothendieckTopology X.carrier)
    CommRingCat.{u}} (b : inverseImageBaseRing (f ≫ t) ⟶ R) (φ : R ⟶ X.sheaf)
    (h : b ≫ φ = structureRingMap (f ≫ t)) (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) :
    (b.hom.app _).hom (((baseUnit (f ≫ t)).hom.app V).hom s) ∈
      kernelIdeal φ.hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) := by
  have h1 := congrArg (fun k => (k.hom.app (op ((Opens.map (f ≫ t).hom.base).obj V.unop))).hom
    (((baseUnit (f ≫ t)).hom.app V).hom s)) h
  have h3 : (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (f ≫ t).hom.base).homEquiv _ _ (structureRingMap (f ≫ t)) = ⟨(f ≫ t).hom.c⟩ :=
    Equiv.apply_symm_apply _ _
  have h2 := (homEquiv_app_apply (f ≫ t) (structureRingMap (f ≫ t)) V s).symm.trans
    (congrArg (fun k => (k.hom.app V).hom s) h3)
  show (φ.hom.app _).hom ((b.hom.app _).hom _) = 0
  refine h1.trans (h2.trans ?_)
  show (f.hom.c.app _).hom ((t.hom.c.app V).hom s) = 0
  rw [hs, map_zero]

namespace AlgebraSquareZeroExtension

variable {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (E : AlgebraSquareZeroExtension (f ≫ t) G)

/-- The adjoint of the algebra structure, on sections: the algebra structure applied to the
image under the unit. -/
theorem adjointBase_app_apply (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) :
    (E.adjointBase.hom.app V).hom s =
      (E.base.hom.app _).hom (((baseUnit (f ≫ t)).hom.app V).hom s) :=
  homEquiv_app_apply (f ≫ t) E.base V s

/-- The section of `𝒢` that the algebra structure of an extension carries a section of the ideal
sheaf `𝒥` of `t` to. -/
def idealSection (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    G.val.obj (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) :=
  E.ideal.app _ ⟨(E.adjointBase.hom.app V).hom ((Stacks.ClosedImmersion.idealSheafι t).val.app V y),
    E.adjointBase_mem_kernelIdeal V _ (app_idealSheafι_eq_zero t V y)⟩

/-- The transposed ideal map `𝒥 ⟶ (f ∘ t)_* 𝒢` of an extension: a section of `𝒥` goes to the
section of `𝒢` the algebra structure carries it to. -/
def idealTranspose :
    AlgebraicGeometry.SheafOfModules.idealSheaf t ⟶ (modulePushforward (f ≫ t)).obj G where
  val :=
    { app := fun V => ConcreteCategory.ofHom
        { toFun := E.idealSection V
          map_add' := fun y y' =>
            (congrArg (E.ideal.app _) (Subtype.ext
              ((congrArg (E.adjointBase.hom.app V).hom (map_add _ y y')).trans
                (map_add _ _ _)))).trans (map_add (E.ideal.app _) _ _)
          map_smul' := fun r y => by
            have hr : presentationScalar E.reduction _ ((E.adjointBase.hom.app V).hom r) =
                ((f ≫ t).hom.c.app V).hom r :=
              congrArg (fun k => (k.hom.app V).hom r) E.adjointBase_comp_reduction
            have hx : (⟨(E.adjointBase.hom.app V).hom
                ((Stacks.ClosedImmersion.idealSheafι t).val.app V (r • y)),
                E.adjointBase_mem_kernelIdeal V _ (app_idealSheafι_eq_zero t V (r • y))⟩ :
                  ↥(kernelIdeal E.reduction.hom (op ((Opens.map (f ≫ t).hom.base).obj V.unop)))) =
                (show E.sheaf.obj.obj (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) from
                    (E.adjointBase.hom.app V).hom r) •
                  ⟨(E.adjointBase.hom.app V).hom
                    ((Stacks.ClosedImmersion.idealSheafι t).val.app V y),
                    E.adjointBase_mem_kernelIdeal V _ (app_idealSheafι_eq_zero t V y)⟩ :=
              Subtype.ext ((congrArg (E.adjointBase.hom.app V).hom
                (map_smul ((Stacks.ClosedImmersion.idealSheafι t).val.app V).hom r y)).trans
                (map_mul _ _ _))
            refine (congrArg (E.ideal.app _) hx).trans
              ((E.ideal.app_smul _ ((E.adjointBase.hom.app V).hom r) _).trans ?_)
            rw [hr]
            rfl }
      naturality := fun {V W} k => by
        ext y
        refine Eq.trans ?_ (E.ideal.app_map ((Opens.map (f ≫ t).hom.base).op.map k)
          ⟨_, E.adjointBase_mem_kernelIdeal V _ (app_idealSheafι_eq_zero t V y)⟩)
        refine congrArg (E.ideal.app _) (Subtype.ext ?_)
        exact (congrArg (E.adjointBase.hom.app W).hom
          (PresheafOfModules.naturality_apply (Stacks.ClosedImmersion.idealSheafι t).val k y)).trans
          (NatTrans.naturality_apply E.adjointBase.hom k _) }

/-- On sections over `V`, the transposed ideal map sends `y` to `E.idealSection V y`. -/
theorem idealTranspose_app (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    (E.idealTranspose.val.app V).hom y = E.idealSection V y :=
  rfl

/-- **The ideal map `f^* t^* 𝒥 ⟶ 𝒢` of a square-zero extension of `(f ∘ t)⁻¹𝒪_{S'}`-algebras**:
the transpose, along `(f ∘ t)^* ⊣ (f ∘ t)_*` and `(f ∘ t)^* = f^* t^*`, of the map
`𝒥 ⟶ (f ∘ t)_* 𝒢` carrying a section of `𝒥` to the section of the square-zero ideal its image
under the algebra structure is. -/
def idealMap :
    (modulePullback f).obj
        ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G :=
  (modulePullbackCompUniq f t).inv.app _ ≫
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _).symm E.idealTranspose

/-- The transposed ideal map is the transpose of the ideal map. -/
theorem prescribedIdealMap_idealMap :
    prescribedIdealMap (f := f) (t := t) E.idealMap = E.idealTranspose :=
  (congrArg ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _)
    (Iso.hom_inv_id_app_assoc (modulePullbackCompUniq f t) _ _)).trans
    (Equiv.apply_symm_apply _ _)

end AlgebraSquareZeroExtension

/-! ### Maps out of `f^* t^* 𝒥` and their transposes -/

/-- `f^* t^* 𝒥`, the pullback to `X` of the ideal sheaf `𝒥` of `t`, as a sheaf of modules over
the structure sheaf of `X` read as a sheaf of rings on the opens of `X`. -/
abbrev pulledIdeal (f : X ⟶ S) (t : S ⟶ S') :
    SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf) :=
  (modulePullback f).obj ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t))

section Transpose

variable {G G' : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}

/-- A map out of `f^* t^* 𝒥` is determined by its transpose. -/
theorem prescribedIdealMap_injective {c c' : pulledIdeal f t ⟶ G}
    (h : prescribedIdealMap c = prescribedIdealMap c') : c = c' :=
  (cancel_epi ((modulePullbackCompUniq f t).hom.app _)).1
    (((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _).injective h)

/-- The transpose of a composite is the transpose followed by the pushforward. -/
theorem prescribedIdealMap_comp (c : pulledIdeal f t ⟶ G) (ψ : G ⟶ G') :
    prescribedIdealMap (c ≫ ψ) = prescribedIdealMap c ≫ (modulePushforward (f ≫ t)).map ψ :=
  (congrArg ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _)
    (Category.assoc _ _ _).symm).trans
    ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv_naturality_right _ _)

/-- The transpose of zero is zero. -/
theorem prescribedIdealMap_zero :
    prescribedIdealMap (f := f) (t := t) (0 : pulledIdeal f t ⟶ G) = 0 :=
  (congrArg ((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv _ _) comp_zero).trans
    (((modulePullbackPushforwardAdjunction (f ≫ t)).homEquiv_unit _ _ _).trans
      ((congrArg ((modulePullbackPushforwardAdjunction (f ≫ t)).unit.app _ ≫ ·)
        ((modulePushforward (f ≫ t)).map_zero _ _)).trans comp_zero))

/-- The transpose of a composite, on sections. -/
theorem prescribedIdealMap_comp_app (c : pulledIdeal f t ⟶ G) (ψ : G ⟶ G')
    (V : (Opens S'.carrier)ᵒᵖ) (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    ((prescribedIdealMap (c ≫ ψ)).val.app V).hom y =
      (ψ.val.app _).hom (((prescribedIdealMap c).val.app V).hom y) :=
  congrArg (fun k => (k.val.app V).hom y) (prescribedIdealMap_comp c ψ)

/-- The transpose of zero vanishes on sections. -/
theorem prescribedIdealMap_zero_app (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    ((prescribedIdealMap (f := f) (t := t) (0 : pulledIdeal f t ⟶ G)).val.app V).hom y = 0 :=
  congrArg (fun k => (k.val.app V).hom y) (prescribedIdealMap_zero (f := f) (t := t) (G := G))

/-- Two maps out of `f^* t^* 𝒥` agree as soon as their transposes agree on sections. -/
theorem prescribedIdealMap_ext {c c' : pulledIdeal f t ⟶ G}
    (h : ∀ (V : (Opens S'.carrier)ᵒᵖ)
      (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V),
      ((prescribedIdealMap c).val.app V).hom y = ((prescribedIdealMap c').val.app V).hom y) :
    c = c' :=
  prescribedIdealMap_injective (by ext V y; exact h V y)

/-- A composite `c ≫ ψ` with a map out of `f^* t^* 𝒥` is `c'` as soon as `ψ` carries the transpose
of `c` to the transpose of `c'` on sections. -/
private theorem comp_eq_of_prescribedIdealMap_comp_app {c : pulledIdeal f t ⟶ G}
    {c' : pulledIdeal f t ⟶ G'} (ψ : G ⟶ G')
    (h : ∀ (V : (Opens S'.carrier)ᵒᵖ)
      (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V),
      (ψ.val.app _).hom (((prescribedIdealMap c).val.app V).hom y) =
        ((prescribedIdealMap c').val.app V).hom y) :
    c ≫ ψ = c' :=
  prescribedIdealMap_ext fun V y => (prescribedIdealMap_comp_app _ _ V y).trans (h V y)

end Transpose

namespace AlgebraSquareZeroExtension

variable {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  (E : AlgebraSquareZeroExtension (f ≫ t) G)

/-- **The ideal map of an extension is `c` exactly when the extension induces `c` on sections of
`𝒥`**: for every section `s` of `𝒪_{S'}` killed by `t^♯`, the section of the square-zero ideal
the algebra structure carries `s` to is the value of `c` on `s`. -/
theorem idealMap_eq_iff
    (c : (modulePullback f).obj
      ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G) :
    E.idealMap = c ↔
      ∀ (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V) (hs : (t.hom.c.app V).hom s = 0),
        E.ideal.app _ ⟨(E.adjointBase.hom.app V).hom s, E.adjointBase_mem_kernelIdeal V s hs⟩ =
          prescribedIdealSection c V s hs := by
  constructor
  · rintro rfl V s hs
    refine Eq.trans ?_ (congrArg (fun k => (k.val.app V).hom (baseIdealSection t V s hs))
      E.prescribedIdealMap_idealMap).symm
    refine congrArg (E.ideal.app _) (Subtype.ext ?_)
    exact congrArg (E.adjointBase.hom.app V).hom (idealSheafι_baseIdealSection t V s hs).symm
  · intro hc
    refine prescribedIdealMap_injective (E.prescribedIdealMap_idealMap.trans ?_)
    ext V y
    set s := (Stacks.ClosedImmersion.idealSheafι t).val.app V y
    have hs : (t.hom.c.app V).hom s = 0 := app_idealSheafι_eq_zero t V y
    have hy : y = baseIdealSection t V s hs :=
      Stacks.ClosedImmersion.injective_idealSheafι_val_app t V.unop
        (idealSheafι_baseIdealSection t V s hs).symm
    refine (hc V s hs).trans ?_
    show (prescribedIdealMap c).val.app V (baseIdealSection t V s hs) =
      (prescribedIdealMap c).val.app V y
    rw [← hy]

end AlgebraSquareZeroExtension

namespace DeformationSolution

variable {ht : IsFirstOrderThickening t} {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}
  (Q : DeformationSolution t ht f G c)

/-- **The ideal map of the extension attached to a solution is the prescribed map `c`.** -/
theorem toAlgebraExtension_idealMap : Q.toAlgebraExtension.idealMap = c :=
  (Q.toAlgebraExtension.idealMap_eq_iff c).2 Q.toAlgebraExtension_ideal_adjointBase

end DeformationSolution

/-! ### The map into the conormal sheaf of a presentation -/

section Presentation

variable (f t) (E : Functor (Opens X.carrier)ᵒᵖ (Type u))
  (α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation (f ≫ t) E α).hom]

/-- The conormal sheaf `𝒥'/𝒥'²` of the presentation `(f ∘ t)⁻¹𝒪_{S'}[ℰ] ⟶ 𝒪_X`. -/
abbrev presentationConormal :
    SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf) :=
  Stacks.Sites.Conormal.conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E)
    X.sheaf (generatorsPresentation (f ≫ t) E α)

omit [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation (f ≫ t) E α).hom] in
/-- The coefficient image in `(f ∘ t)⁻¹𝒪_{S'}[ℰ]` of a section of `𝒪_{S'}` killed by `t^♯` is a
local relation of the presentation. -/
theorem coefficient_mem_kernelIdeal (V : (Opens S'.carrier)ᵒᵖ) (s : S'.presheaf.obj V)
    (hs : (t.hom.c.app V).hom s = 0) :
    ((freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E).hom.app _).hom
        (((baseUnit (f ≫ t)).hom.app V).hom s) ∈
      kernelIdeal (generatorsPresentation (f ≫ t) E α).hom
        (op ((Opens.map (f ≫ t).hom.base).obj V.unop)) :=
  baseUnit_mem_kernelIdeal _ _ (freeAlgebraSheafCoefficientMap_comp_desc
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf E
    (structureRingMap (f ≫ t)) α) V s hs

/-- The conormal class in `𝒥'/𝒥'²` of the coefficient image of a section of `𝒥`. -/
def coefficientConormalClass (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :=
  Stacks.Sites.Conormal.conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing (f ≫ t))
    (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E)
    X.sheaf (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E) (generatorsPresentation (f ≫ t) E α)
    (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
    ⟨_, coefficient_mem_kernelIdeal f t E α V _
        (app_idealSheafι_eq_zero t V y)⟩

/-- **The section of `𝒢` that the extension attached to a conormal homomorphism `δ` carries a
section of `𝒥` to is the value of `δ` on the conormal class of its coefficient image**: the
algebra structure of the square-zero pushout is the inclusion of the coefficients followed by
`r ↦ [(r, 0)]`, which on a local relation is the image of `δ` of its class. -/
theorem idealSection_extensionOfConormalHom
    {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
    (δ : presentationConormal f t E α ⟶ G) (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    (extensionOfConormalHom.{u} δ).idealSection V y =
      (δ.val.app _).hom (coefficientConormalClass f t E α V y) :=
  Stacks.Sites.SqZeroPushout.idealRestriction_app_eq_of_val.{u}
    (generatorsPresentation (f ≫ t) E α) G (conormalPushoutData.{u} δ) _ _ _
    (((extensionOfConormalHom.{u} δ).adjointBase_app_apply V
      ((Stacks.ClosedImmersion.idealSheafι t).val.app V y)).trans
      (Stacks.Sites.SqZeroPushout.pushoutInl_app_kernel.{u} (generatorsPresentation (f ≫ t) E α)
        (Stacks.Sites.SqZeroPushout.restrictAlong.{u} (generatorsPresentation (f ≫ t) E α) G)
        (conormalPushoutData.{u} δ) _
        ⟨_, coefficient_mem_kernelIdeal f t E α V _
          (app_idealSheafι_eq_zero t V y)⟩))

/-- The universal square-zero extension of a presentation: the square-zero pushout of
`(f ∘ t)⁻¹𝒪_{S'}[ℰ]` along the identity of its conormal sheaf, an extension of `𝒪_X` by
`𝒥'/𝒥'²`. -/
abbrev presentationExtension :
    AlgebraSquareZeroExtension (f ≫ t) (presentationConormal f t E α) :=
  extensionOfConormalHom.{u} (𝟙 (presentationConormal f t E α))

/-- **The map `f^* t^* 𝒥 ⟶ 𝒥'/𝒥'²` into the conormal sheaf of a presentation**, with
`𝒥'/𝒥'²` read as the first term of the conormal sequence: the ideal map of the universal
square-zero extension of the presentation. Its transpose sends a section of `𝒥` to the conormal
class of its coefficient image (`prescribedIdealMap_presentationIdealMap`). -/
def presentationIdealMap :
    pulledIdeal f t ⟶ (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf
      (structureRingMap (f ≫ t)) E α).X₁ :=
  (presentationExtension f t E α).idealMap

/-- The transpose of `presentationIdealMap` sends a section of `𝒥` to the conormal class of its
coefficient image. -/
theorem prescribedIdealMap_presentationIdealMap (V : (Opens S'.carrier)ᵒᵖ)
    (y : (AlgebraicGeometry.SheafOfModules.idealSheaf t).val.obj V) :
    ((prescribedIdealMap (presentationIdealMap f t E α)).val.app V).hom y =
      coefficientConormalClass f t E α V y :=
  (congrArg (fun k => (k.val.app V).hom y)
    (AlgebraSquareZeroExtension.prescribedIdealMap_idealMap (presentationExtension f t E α))).trans
    (idealSection_extensionOfConormalHom f t E α (𝟙 _) V y)

/-- The map into the conormal sheaf is killed by `𝒥'/𝒥'² ⟶ Ω ⊗ 𝒪_X`: the coefficients have zero
differential. -/
theorem presentationIdealMap_comp_conormalSequence_f :
    presentationIdealMap f t E α ≫ (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf
      (structureRingMap (f ≫ t)) E α).f = 0 := by
  refine comp_eq_of_prescribedIdealMap_comp_app _ (fun V y => ?_)
  rw [prescribedIdealMap_zero_app, prescribedIdealMap_presentationIdealMap]
  exact Stacks.Sites.Conormal.conormalSequence_f_conormalClass_coefficient.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) _ _ _ _ _ _ _ _

/-- The chain map `(f^* t^* 𝒥)[-1] ⟶ 𝖭𝖫(α)` whose degree `-1` component is
`presentationIdealMap`. -/
abbrev presentationIdealChainMap :
    (HomologicalComplex.single
        (SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf))
        (ComplexShape.up ℤ) (-1)).obj (pulledIdeal f t) ⟶
      HomologicalComplex.double (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf
        (structureRingMap (f ≫ t)) E α).f
        ComplexShape.upIntRelNegOneZero :=
  CochainComplex.singleNegOneToDouble _ (presentationIdealMap f t E α)
    (presentationIdealMap_comp_conormalSequence_f f t E α)

/-- A morphism of presentations carries the map into the conormal sheaf of the first to the one
of the second: both send a section of `𝒥` to the conormal class of its coefficient image, and a
morphism of free algebras over `(f ∘ t)⁻¹𝒪_{S'}` fixes the coefficients. -/
theorem presentationIdealMap_comp_presentationConormalMap
    {E₁ E₂ : Functor (Opens X.carrier)ᵒᵖ (Type u)}
    (h : E₁ ⟶ E₂) {α₁ : E₁ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
    {α₂ : E₂ ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation (f ≫ t) E₁ α₁).hom]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
      (generatorsPresentation (f ≫ t) E₂ α₂).hom] (hα : h ≫ α₂ = α₁) :
    presentationIdealMap f t E₁ α₁ ≫
        Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u}
          (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E₁ E₂ h X.sheaf
          (structureRingMap (f ≫ t)) α₁ α₂ hα =
      presentationIdealMap f t E₂ α₂ := by
  refine comp_eq_of_prescribedIdealMap_comp_app _ (fun V y => ?_)
  rw [prescribedIdealMap_presentationIdealMap, prescribedIdealMap_presentationIdealMap]
  have := Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass_coefficient.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t))
    (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E₁)
    X.sheaf (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E₁) (generatorsPresentation (f ≫ t) E₁ α₁)
    (op ((Opens.map (f ≫ t).hom.base).obj V.unop))
    (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E₂)
    (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
        (inverseImageBaseRing (f ≫ t)) E₂) (generatorsPresentation (f ≫ t) E₂ α₂)
    (Stacks.SheafOfModules.freeAlgebraMap _ _ E₁ E₂ h)
    (Stacks.SheafOfModules.freeAlgebraMap_comp_presentation _ _ E₁ E₂ h _ _ α₁ α₂ hα)
    (Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) E₁ E₂ h)
    (((baseUnit (f ≫ t)).hom.app V).hom ((Stacks.ClosedImmersion.idealSheafι t).val.app V y))
    (coefficient_mem_kernelIdeal f t E₁ α₁ V _
      (app_idealSheafι_eq_zero t V y))
    (coefficient_mem_kernelIdeal f t E₂ α₂ V _
      (app_idealSheafι_eq_zero t V y))
  exact this

/-- **The map into the conormal sheaf of the presentation of an extension, followed by the
homomorphism `𝒥/𝒥² ⟶ 𝒢` of the extension, is the ideal map of the extension**: the lift
`(f ∘ t)⁻¹𝒪_{S'}[ℰ] ⟶ 𝒪_{X'}` restricts on the coefficients to the algebra structure. -/
theorem presentationIdealMap_comp_conormalToIdeal
    {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
    (P : AlgebraSquareZeroExtension (f ≫ t) G) :
    presentationIdealMap f t P.generators P.generatorsMap ≫ P.toPresented.conormalToIdeal =
      P.idealMap := by
  refine comp_eq_of_prescribedIdealMap_comp_app _ (fun V y => ?_)
  rw [prescribedIdealMap_presentationIdealMap,
    AlgebraSquareZeroExtension.prescribedIdealMap_idealMap]
  refine (Stacks.Sites.Conormal.conormalDesc_conormalClass _ G _ _ _ _ _).trans ?_
  refine congrArg (P.ideal.app _) (Subtype.ext ?_)
  exact (congrArg (fun k => (k.hom.app _).hom (((baseUnit (f ≫ t)).hom.app V).hom
      ((Stacks.ClosedImmersion.idealSheafι t).val.app V y)))
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing (f ≫ t)) P.sheaf P.generators P.base (𝟙 _))).trans
    (P.adjointBase_app_apply V _).symm

end Presentation

/-! ### The map `f^* t^* 𝒥 ⟶ 𝒥'/𝒥'²` into the naive cotangent complex -/

section Canonical

variable (f t)

/-- **The map `f^* t^* 𝒥 ⟶ 𝒥'/𝒥'²` into the degree `-1` term of `𝖭𝖫_{X/S'}`**, the conormal
sheaf of the canonical presentation `(f ∘ t)⁻¹𝒪_{S'}[𝒪_X] ⟶ 𝒪_X`: its transpose sends a section
`s` of `𝒥` to the conormal class of the coefficient image of `s`
(`prescribedIdealMap_presentationIdealMap`). -/
def idealConormalMap : pulledIdeal f t ⟶ (RingedSpace.naiveCotangentComplex (f ≫ t)).X (-1) :=
  presentationIdealMap f t (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
      (𝟙 _) ≫
    (HomologicalComplex.doubleXIso₀ _ ComplexShape.upIntRelNegOneZero).inv

/-- The chain map `(f^* t^* 𝒥)[-1] ⟶ 𝖭𝖫_{X/S'}` whose degree `-1` component is
`idealConormalMap`. -/
def idealConormalChainMap :
    (HomologicalComplex.single
        (SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf))
        (ComplexShape.up ℤ) (-1)).obj (pulledIdeal f t) ⟶
      RingedSpace.naiveCotangentComplex (f ≫ t) :=
  presentationIdealChainMap f t (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf)
    (𝟙 _)

/-- The degree `-1` component of `idealConormalChainMap f t` is `idealConormalMap f t`. -/
theorem idealConormalChainMap_f :
    (idealConormalChainMap f t).f (-1) =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) _).hom ≫ idealConormalMap f t :=
  CochainComplex.singleNegOneToDouble_f _ _ (presentationIdealMap_comp_conormalSequence_f f t _ _)

/-- **The map into the conormal term is killed by the differential of `𝖭𝖫_{X/S'}`**: the
coefficients of `(f ∘ t)⁻¹𝒪_{S'}[𝒪_X]` have zero differential. -/
theorem idealConormalMap_comp_d :
    idealConormalMap f t ≫ (RingedSpace.naiveCotangentComplex (f ≫ t)).d (-1) 0 = 0 := by
  have h := (idealConormalChainMap f t).comm (-1) 0
  rw [idealConormalChainMap_f, HomologicalComplex.single_obj_d, zero_comp, Category.assoc] at h
  exact (cancel_epi _).1 (h.trans comp_zero.symm)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The map `(f^* t^* 𝒥)[1] ⟶ 𝖭𝖫_{X/S'}` in `D(𝒪_X)`**: the identification
`(f^* t^* 𝒥)[0]⟦1⟧ ≅ (f^* t^* 𝒥)[-1]` followed by the chain map with degree `-1` component
`idealConormalMap`. -/
def idealToNaiveCotangent :
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)) 0).obj
        (pulledIdeal f t))⟦(1 : ℤ)⟧ ⟶ PresentedSquareZeroExtension.relativeObj (f ≫ t) :=
  (CochainComplex.singleZeroShiftOneIso (pulledIdeal f t)).hom ≫
    DerivedCategory.Q.map (idealConormalChainMap f t)

/-- `idealToNaiveCotangent f t` is the identification `(f^* t^* 𝒥)[0]⟦1⟧ ≅ (f^* t^* 𝒥)[-1]`
followed by the image of `idealConormalChainMap f t` in the derived category. -/
theorem idealToNaiveCotangent_eq :
    idealToNaiveCotangent f t =
      (CochainComplex.singleZeroShiftOneIso (pulledIdeal f t)).hom ≫
        DerivedCategory.Q.map (idealConormalChainMap f t) :=
  rfl

/-- The two spellings `𝖭𝖫_{X/S'}` of the naive cotangent complex of a morphism of ringed spaces
in `D(𝒪_X)` agree: the two spellings of the structure map agree
(`Stacks.NaiveCotangentFlatBaseChange.ringedSpaceStructureMap_eq_inverseImageStructureMap`). -/
def relativeNaiveCotangentObjIso (g : X ⟶ S') :
    relativeNaiveCotangentObj g ≅ PresentedSquareZeroExtension.relativeObj g :=
  Iso.refl _

/-- **The class of a square-zero extension restricted along `(f^* t^* 𝒥)[1] ⟶ 𝖭𝖫_{X/S'}` is
minus the shifted ideal map of the extension.** The map into the conormal term of the canonical
presentation factors through the presentation of the extension, and there the class of the
extension is the projection onto the shifted conormal term followed by the homomorphism
`𝒥/𝒥² ⟶ 𝒢`; the sign is that of the triangle of a mapping cone
(`CochainComplex.singleZeroShiftOneIso_hom_comp_doubleProjQ`). -/
theorem idealToNaiveCotangent_comp_extClass
    {G : SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
    (P : AlgebraSquareZeroExtension (f ≫ t) G) :
    idealToNaiveCotangent f t ≫ P.toPresented.extClass =
      -(((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (ringSheaf (J := Opens.grothendieckTopology X.carrier) X.sheaf)) 0).map
          P.idealMap)⟦(1 : ℤ)⟧') := by
  have hcomp := presentationIdealMap_comp_presentationConormalMap f t P.generatorsMap
    (α₂ := 𝟙 (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf))
    (Category.comp_id _)
  have hφ :=
    Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne_doubleXIso₀.{u, u, u, u}
      (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) P.generators
      (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) P.generatorsMap X.sheaf
      (structureRingMap (f ≫ t)) P.generatorsMap (𝟙 _) (Category.comp_id _)
  have ha' := presentationIdealMap_comp_conormalSequence_f f t
    (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _)
  have ha'' : (presentationIdealMap f t P.generators P.generatorsMap ≫
      Stacks.SheafOfModules.presentationConormalMap.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) P.generators
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) P.generatorsMap X.sheaf
        (structureRingMap (f ≫ t)) P.generatorsMap (𝟙 _) (Category.comp_id _)) ≫
      (Stacks.SheafOfModules.presentationConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf
        (structureRingMap (f ≫ t))
        (underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf) (𝟙 _)).f = 0 := by
    rw [hcomp]
    exact ha'
  have hA : presentationIdealChainMap f t P.generators P.generatorsMap ≫
      Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
        (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing (f ≫ t)) X.sheaf
        (structureRingMap (f ≫ t)) P.generators P.generatorsMap = idealConormalChainMap f t :=
    (CochainComplex.singleNegOneToDouble_comp _ _ _
      (presentationIdealMap_comp_conormalSequence_f f t P.generators P.generatorsMap) _ _ hφ
      ha'').trans (CochainComplex.singleNegOneToDouble_congr _ ha'' ha' hcomp)
  have hQ : DerivedCategory.Q.map (idealConormalChainMap f t) ≫
      (PresentedSquareZeroExtension.naiveCotangentIso (f ≫ t) P.generators P.generatorsMap).inv =
      DerivedCategory.Q.map (presentationIdealChainMap f t P.generators P.generatorsMap) :=
    (Iso.comp_inv_eq _).2 ((congrArg DerivedCategory.Q.map hA).symm.trans (Functor.map_comp _ _ _))
  have hB := CochainComplex.singleZeroShiftOneIso_hom_comp_singleNegOneToDouble_comp_doubleProjQ
    _ (presentationIdealMap f t P.generators P.generatorsMap)
    (presentationIdealMap_comp_conormalSequence_f f t P.generators P.generatorsMap)
  have hC := presentationIdealMap_comp_conormalToIdeal f t P
  unfold idealToNaiveCotangent PresentedSquareZeroExtension.extClass
    PresentedSquareZeroExtension.presentedExtClass NaiveCotangentTwoTerm.conormalExtClass
  refine (comp_comp_comp_eq_neg (CochainComplex.singleZeroShiftOneIso (pulledIdeal f t)).hom
    (DerivedCategory.Q.map (idealConormalChainMap f t))
    (PresentedSquareZeroExtension.naiveCotangentIso (f ≫ t) P.generators P.generatorsMap).inv
    (DerivedCategory.Q.map (presentationIdealChainMap f t P.generators P.generatorsMap))
    (PresentedSquareZeroExtension.twoTerm (f ≫ t) P.generators P.generatorsMap).proj
    _ _ hQ hB).trans (congrArg Neg.neg ?_)
  refine ((shiftFunctor _ (1 : ℤ)).map_comp _ _).symm.trans ?_
  refine congrArg (shiftFunctor _ (1 : ℤ)).map
    (((DerivedCategory.singleFunctor _ 0).map_comp _ _).symm.trans ?_)
  exact congrArg (DerivedCategory.singleFunctor _ 0).map hC

end Derived

end Canonical

end AlgebraicGeometry.RingedSpaceThickening

end
