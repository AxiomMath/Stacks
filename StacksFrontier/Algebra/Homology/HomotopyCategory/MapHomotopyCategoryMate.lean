module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.AlongAnIsomorphism

/-!
# Mates of degreewise squares on homotopy categories

An adjunction `E ⊣ P` of additive functors induces an adjunction `E ⊣ P` on homotopy categories
(`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction`), and a square of additive functors
built from composition isomorphisms induces a square on homotopy categories. This file shows that
passing to homotopy categories commutes with taking mates: at the class of a complex `K`, the
inverse mate of the induced square is the class of the degreewise inverse mate of the original
square. In particular the induced inverse mate is invertible as soon as the original one is.

## Main results

* `CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction_ofNatIsoRight`: renaming the right
  adjoint commutes with passing to homotopy categories.
* `CategoryTheory.Functor.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso`: the
  composition isomorphism on homotopy categories followed by an induced isomorphism is the
  composition isomorphism of the composite.
* `CategoryTheory.Adjunction.mateEquiv_symm_mapHomotopyCategoryCompIso_app_quotient`: the inverse
  mate of an induced square, at the class of a complex.
* `CategoryTheory.Adjunction.isIso_mateEquiv_symm_mapHomotopyCategory_app`: the inverse mate of an
  induced square is invertible when the original inverse mate is;
  `CategoryTheory.Adjunction.isIso_mateEquiv_symm_app_of_eq_mapHomotopyCategory` is the same for
  adjunctions and squares on homotopy categories given as data identified with the induced ones.
* `CategoryTheory.NatTrans.isIso_app_of_heq`: invertibility of components transfers along a
  heterogeneous equality of natural transformations between equal functors.
-/

@[expose] public section

open CategoryTheory Category Functor

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace Adjunction

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B]

/-- Renaming the right adjoint of an adjunction of additive functors commutes with passing to
homotopy categories. -/
theorem mapHomotopyCategoryAdjunction_ofNatIsoRight {E : B ⥤ A} {R P : A ⥤ B} [E.Additive]
    [R.Additive] [P.Additive] (adj : E ⊣ R) (ι : P ≅ R) (c : ComplexShape ℤ) :
    (mapHomotopyCategoryAdjunction adj c).ofNatIsoRight
        (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ι c).symm =
      mapHomotopyCategoryAdjunction (adj.ofNatIsoRight ι.symm) c := by
  apply Adjunction.ext
  apply Quotient.natTrans_ext
  ext K
  show ((mapHomotopyCategoryAdjunction adj c).ofNatIsoRight
      (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ι c).symm).unit.app
        ((HomotopyCategory.quotient B c).obj K) =
    (mapHomotopyCategoryAdjunction (adj.ofNatIsoRight ι.symm) c).unit.app
      ((HomotopyCategory.quotient B c).obj K)
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_id,
    mapHomotopyCategoryAdjunction_unit_app_quotient,
    mapHomotopyCategoryAdjunction_unit_app_quotient]
  have h : (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ι c).symm.hom.app
      ((E.mapHomotopyCategory c).obj ((HomotopyCategory.quotient B c).obj K)) =
      (HomotopyCategory.quotient B c).map
        ((NatTrans.mapHomologicalComplex ι.inv c).app ((E.mapHomologicalComplex c).obj K)) := rfl
  rw [h]
  show (HomotopyCategory.quotient B c).map
      ((mapHomologicalComplexAdjunction adj c).unit.app K ≫
        (NatTrans.mapHomologicalComplex ι.inv c).app ((E.mapHomologicalComplex c).obj K)) = _
  refine congrArg (HomotopyCategory.quotient B c).map ?_
  ext n
  simp [mapHomologicalComplexAdjunction, ← Adjunction.homEquiv_id]

end Adjunction

namespace Functor

variable {V : Type u₁} [Category.{v₁} V] [Preadditive V]
  {W : Type u₂} [Category.{v₂} W] [Preadditive W]
  {W' : Type u₃} [Category.{v₃} W'] [Preadditive W']

/-- The composition isomorphism on homotopy categories followed by an induced isomorphism is the
composition isomorphism of the composite. -/
theorem mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso {F : V ⥤ W} {G : W ⥤ W'}
    {H H' : V ⥤ W'} [F.Additive] [G.Additive] [H.Additive] [H'.Additive] (e : F ⋙ G ≅ H)
    (τ : H ≅ H') (c : ComplexShape ℤ) :
    Functor.mapHomotopyCategoryCompIso e c ≪≫ Stacks.Homology.mapHomotopyCategoryIso τ c =
      Functor.mapHomotopyCategoryCompIso (e ≪≫ τ) c := by
  apply Iso.ext
  ext X
  obtain ⟨K⟩ := X
  refine (((HomotopyCategory.quotient W' c).map_comp _ _).symm).trans ?_
  refine congrArg (HomotopyCategory.quotient W' c).map ?_
  ext n
  simp [Functor.mapHomologicalComplexCompIso]

end Functor

namespace Adjunction

variable {CZ : Type u₁} [Category.{v₁} CZ] [Preadditive CZ]
  {CU : Type u₂} [Category.{v₂} CU] [Preadditive CU]
  {CT : Type u₃} [Category.{v₃} CT] [Preadditive CT]
  {CT' : Type u₄} [Category.{v₄} CT'] [Preadditive CT']

/-- **The inverse mate of a square induced on homotopy categories, at the class of a complex**,
is the class of the degreewise inverse mate of the original square. -/
theorem mateEquiv_symm_mapHomotopyCategoryCompIso_app_quotient {ι : Type*} (c : ComplexShape ι)
    {E : CU ⥤ CZ} {P : CZ ⥤ CU} {E' : CT' ⥤ CT} {P' : CT ⥤ CT'} {Pt : CZ ⥤ CT}
    {Pt' : CU ⥤ CT'} {Pa : CZ ⥤ CT'} [E.Additive] [P.Additive] [E'.Additive] [P'.Additive]
    [Pt.Additive] [Pt'.Additive] [Pa.Additive] (adj : E ⊣ P) (adj' : E' ⊣ P')
    (c₁ : P ⋙ Pt' ≅ Pa) (c₂ : Pt ⋙ P' ≅ Pa) (K : HomologicalComplex CU c) :
    ((mateEquiv (mapHomotopyCategoryAdjunction adj c) (mapHomotopyCategoryAdjunction adj' c)).symm
        (TwoSquare.mk _ _ _ _ ((Functor.mapHomotopyCategoryCompIso c₁ c).hom ≫
          (Functor.mapHomotopyCategoryCompIso c₂ c).inv))).natTrans.app
        ((HomotopyCategory.quotient CU c).obj K) =
      (HomotopyCategory.quotient CT c).map ((NatTrans.mapHomologicalComplex
        ((mateEquiv adj adj').symm
          (TwoSquare.mk _ _ _ _ (c₁.hom ≫ c₂.inv))).natTrans c).app K) := by
  simp only [mateEquiv, Equiv.coe_fn_symm_mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, Functor.map_id, Category.id_comp]
  show (HomotopyCategory.quotient CT c).map
      ((E'.mapHomologicalComplex c).map ((Pt'.mapHomologicalComplex c).map
          ((mapHomologicalComplexAdjunction adj c).unit.app K)) ≫
        (E'.mapHomologicalComplex c).map
          ((NatIso.mapHomologicalComplex c₁ c).hom.app ((E.mapHomologicalComplex c).obj K) ≫
            (NatIso.mapHomologicalComplex c₂ c).inv.app ((E.mapHomologicalComplex c).obj K)) ≫
        (mapHomologicalComplexAdjunction adj' c).counit.app
          ((Pt.mapHomologicalComplex c).obj ((E.mapHomologicalComplex c).obj K)) ≫ 𝟙 _) = _
  refine congrArg (HomotopyCategory.quotient CT c).map ?_
  ext n
  simp [mapHomologicalComplexAdjunction]

end Adjunction

namespace Adjunction

/-- **The inverse mate of a degreewise square on homotopy categories is invertible when the
underived inverse mate is.**  Let `E ⊣ R`, `E' ⊣ R'` be adjunctions of additive functors with right
adjoints renamed along `ιu : P ≅ R`, `ιu' : P' ≅ R'`, and let a square `P ⋙ Pt' ⟶ Pt ⋙ P'` be built
from composition isomorphisms `c₁`, `c₂`, comparisons `τ₁`, `τ₂` and an equality `e` of functors.
If the inverse mate of this square is invertible, so is, at every object, the inverse mate of the
square it induces on homotopy categories across the induced adjunctions. -/
theorem isIso_mateEquiv_symm_mapHomotopyCategory_app {CZ : Type u₁} {CU : Type u₂}
    {CT : Type u₃} {CT' : Type u₄} {_ : Category.{v₁} CZ} {_ : Category.{v₂} CU}
    {_ : Category.{v₃} CT} {_ : Category.{v₄} CT'} {_ : Preadditive CZ} {_ : Preadditive CU}
    {_ : Preadditive CT} {_ : Preadditive CT'} {E : CU ⥤ CZ} {R P : CZ ⥤ CU}
    {E' : CT' ⥤ CT} {R' P' : CT ⥤ CT'} {Pt : CZ ⥤ CT} {Pt' : CU ⥤ CT'} {Pc₁ Pc₂ Pa Pb : CZ ⥤ CT'}
    {_ : E.Additive} {_ : R.Additive} {_ : P.Additive} {_ : E'.Additive} {_ : R'.Additive}
    {_ : P'.Additive} {_ : Pt.Additive} {_ : Pt'.Additive} {_ : Pc₁.Additive} {_ : Pc₂.Additive}
    {_ : Pa.Additive} {_ : Pb.Additive}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (ιu : P ≅ R) (ιu' : P' ≅ R') (c₁ : P ⋙ Pt' ≅ Pc₁)
    (τ₁ : Pc₁ ≅ Pa) (e : Pa = Pb) (c₂ : Pt ⋙ P' ≅ Pc₂) (τ₂ : Pc₂ ≅ Pb) (c : ComplexShape ℤ)
    (eh : Pa.mapHomotopyCategory c = Pb.mapHomotopyCategory c)
    (eh' : Pb.mapHomotopyCategory c = Pb.mapHomotopyCategory c)
    (hβ : IsIso ((mateEquiv (adj.ofNatIsoRight ιu.symm) (adj'.ofNatIsoRight ιu'.symm)).symm
      (TwoSquare.mk _ _ _ _ ((c₁ ≪≫ τ₁).hom ≫ eqToHom e ≫ (c₂ ≪≫ τ₂).inv))).natTrans)
    (X : HomotopyCategory CU c) :
    IsIso (((mateEquiv ((mapHomotopyCategoryAdjunction adj c).ofNatIsoRight
          (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ιu c).symm)
        ((mapHomotopyCategoryAdjunction adj' c).ofNatIsoRight
          (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ιu' c).symm)).symm
      (TwoSquare.mk _ _ _ _ ((Functor.mapHomotopyCategoryCompIso c₁ c ≪≫
          Stacks.Homology.mapHomotopyCategoryIso τ₁ c ≪≫ eqToIso eh).hom ≫
        (Functor.mapHomotopyCategoryCompIso c₂ c ≪≫
          Stacks.Homology.mapHomotopyCategoryIso τ₂ c ≪≫ eqToIso eh').inv))).natTrans.app X) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp] at hβ
  rw [eqToIso_refl, Iso.trans_refl, Iso.trans_refl,
    Functor.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso,
    Functor.mapHomotopyCategoryCompIso_trans_mapHomotopyCategoryIso,
    mapHomotopyCategoryAdjunction_ofNatIsoRight, mapHomotopyCategoryAdjunction_ofNatIsoRight]
  obtain ⟨K⟩ := X
  rw [show (⟨K⟩ : HomotopyCategory CU c) = (HomotopyCategory.quotient CU c).obj K from rfl,
    mateEquiv_symm_mapHomotopyCategoryCompIso_app_quotient]
  have : IsIso ((NatTrans.mapHomologicalComplex
      ((mateEquiv (adj.ofNatIsoRight ιu.symm) (adj'.ofNatIsoRight ιu'.symm)).symm
        (TwoSquare.mk _ _ _ _ ((c₁ ≪≫ τ₁).hom ≫ (c₂ ≪≫ τ₂).inv))).natTrans c).app K) :=
    have : ∀ n, IsIso (((NatTrans.mapHomologicalComplex
        ((mateEquiv (adj.ofNatIsoRight ιu.symm) (adj'.ofNatIsoRight ιu'.symm)).symm
          (TwoSquare.mk _ _ _ _ ((c₁ ≪≫ τ₁).hom ≫ (c₂ ≪≫ τ₂).inv))).natTrans c).app K).f n) :=
      fun n ↦ NatIso.isIso_app_of_isIso
        ((mateEquiv (adj.ofNatIsoRight ιu.symm) (adj'.ofNatIsoRight ιu'.symm)).symm
          (TwoSquare.mk _ _ _ _ ((c₁ ≪≫ τ₁).hom ≫ (c₂ ≪≫ τ₂).inv))).natTrans (K.X n)
    HomologicalComplex.Hom.isIso_of_components _
  exact Functor.map_isIso _ _

/-- `CategoryTheory.Adjunction.isIso_mateEquiv_symm_mapHomotopyCategory_app` for adjunctions and
identifications on homotopy categories given as data, together with their identification with the
induced ones. -/
theorem isIso_mateEquiv_symm_app_of_eq_mapHomotopyCategory {CZ : Type u₁} {CU : Type u₂}
    {CT : Type u₃} {CT' : Type u₄} {_ : Category.{v₁} CZ} {_ : Category.{v₂} CU}
    {_ : Category.{v₃} CT} {_ : Category.{v₄} CT'} {_ : Preadditive CZ} {_ : Preadditive CU}
    {_ : Preadditive CT} {_ : Preadditive CT'} {E : CU ⥤ CZ} {R P : CZ ⥤ CU}
    {E' : CT' ⥤ CT} {R' P' : CT ⥤ CT'} {Pt : CZ ⥤ CT} {Pt' : CU ⥤ CT'} {Pc₁ Pc₂ Pa Pb : CZ ⥤ CT'}
    {_ : E.Additive} {_ : R.Additive} {_ : P.Additive} {_ : E'.Additive} {_ : R'.Additive}
    {_ : P'.Additive} {_ : Pt.Additive} {_ : Pt'.Additive} {_ : Pc₁.Additive} {_ : Pc₂.Additive}
    {_ : Pa.Additive} {_ : Pb.Additive}
    (adj : E ⊣ R) (adj' : E' ⊣ R') (ιu : P ≅ R) (ιu' : P' ≅ R') (c₁ : P ⋙ Pt' ≅ Pc₁)
    (τ₁ : Pc₁ ≅ Pa) (e : Pa = Pb) (c₂ : Pt ⋙ P' ≅ Pc₂) (τ₂ : Pc₂ ≅ Pb) (c : ComplexShape ℤ)
    (eh : Pa.mapHomotopyCategory c = Pb.mapHomotopyCategory c)
    (eh' : Pb.mapHomotopyCategory c = Pb.mapHomotopyCategory c)
    (hadj : E.mapHomotopyCategory c ⊣ P.mapHomotopyCategory c)
    (hadj' : E'.mapHomotopyCategory c ⊣ P'.mapHomotopyCategory c)
    (hhadj : hadj = (mapHomotopyCategoryAdjunction adj c).ofNatIsoRight
      (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ιu c).symm)
    (hhadj' : hadj' = (mapHomotopyCategoryAdjunction adj' c).ofNatIsoRight
      (Stacks.Cohomology.DerivedPullbackAlongIso.mapHomotopyCategoryIso ιu' c).symm)
    (F₁ : P.mapHomotopyCategory c ⋙ Pt'.mapHomotopyCategory c ≅ Pb.mapHomotopyCategory c)
    (F₂ : Pt.mapHomotopyCategory c ⋙ P'.mapHomotopyCategory c ≅ Pb.mapHomotopyCategory c)
    (hF₁ : F₁ = Functor.mapHomotopyCategoryCompIso c₁ c ≪≫
      Stacks.Homology.mapHomotopyCategoryIso τ₁ c ≪≫ eqToIso eh)
    (hF₂ : F₂ = Functor.mapHomotopyCategoryCompIso c₂ c ≪≫
      Stacks.Homology.mapHomotopyCategoryIso τ₂ c ≪≫ eqToIso eh')
    (hβ : IsIso ((mateEquiv (adj.ofNatIsoRight ιu.symm) (adj'.ofNatIsoRight ιu'.symm)).symm
      (TwoSquare.mk _ _ _ _ ((c₁ ≪≫ τ₁).hom ≫ eqToHom e ≫ (c₂ ≪≫ τ₂).inv))).natTrans)
    (X : HomotopyCategory CU c) :
    IsIso (((mateEquiv hadj hadj').symm
      (TwoSquare.mk _ _ _ _ (F₁.hom ≫ F₂.inv))).natTrans.app X) := by
  subst hhadj hhadj' hF₁ hF₂
  exact isIso_mateEquiv_symm_mapHomotopyCategory_app adj adj' ιu ιu' c₁ τ₁ e c₂ τ₂ c eh eh' hβ X

end Adjunction

namespace NatTrans

/-- A component of a natural transformation is invertible when the corresponding component of a
heterogeneously equal one, between equal functors, is. -/
theorem isIso_app_of_heq {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F G F' G' : C ⥤ D} (η : F ⟶ G) (η' : F' ⟶ G') (hF : F = F') (hG : G = G')
    (h : HEq η η') (X : C) (hη' : IsIso (η'.app X)) : IsIso (η.app X) := by
  subst hF hG
  cases h
  exact hη'

end NatTrans

end CategoryTheory
