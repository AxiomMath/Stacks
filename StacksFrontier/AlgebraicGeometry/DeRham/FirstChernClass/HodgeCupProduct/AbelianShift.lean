module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeCupProduct.GradedPieceShift

/-!
# The abelian identification of the graded pieces through the shift

The abelian and the module identifications of the graded pieces agree
(`gradedPiecePlusShift_comm`), the identification of a single complex in degree `q` through the
shift (`singleFunctorCompHomologyFunctorShiftIso_app_hom`), and the abelian identification of a
graded piece through the shift (`gradedPiece_shift_abelian`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.SheafOfModules.Tensor (sheafTensor)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The abelian and the module identifications of the graded pieces agree -/

section Bridge

open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct

/-- The preimage under a fully faithful functor of a morphism followed by the inverse of an
isomorphism, mapped back and followed by that isomorphism. -/
lemma map_preimage_comp_hom {V W : Type*} [Category* V] [Category* W] (F : V ⥤ W) [F.Full]
    [F.Faithful] {P Q : V} {Y Z : W} (x₁ : F.obj P ⟶ Y) (x₂ : Y ⟶ Z) (e' : Z ⟶ F.obj Q)
    (e : F.obj Q ⟶ Z) (h : e' ≫ e = 𝟙 Z) : F.map (F.preimage (x₁ ≫ x₂ ≫ e')) ≫ e = x₁ ≫ x₂ := by
  rw [Functor.map_preimage, Category.assoc, Category.assoc, h, Category.comp_id]

/-- The algebra of the left-hand side of `gradedPiecePlusShift_comm`. -/
lemma bridgeL_paste {V : Type*} [Category* V] {P Q R S U W : V} (L₀ : P ⟶ S) (M : P ⟶ Q)
    (TG : Q ⟶ R) (C : R ⟶ S) (Dd : S ⟶ U) (X₁ : R ⟶ W) (X₂ : W ⟶ U) (Y : Q ⟶ W)
    (hL₀ : L₀ = M ≫ TG ≫ C) (key : C ≫ Dd = X₁ ≫ X₂) (hTG : TG ≫ X₁ = Y) :
    L₀ ≫ Dd = M ≫ Y ≫ X₂ := by
  rw [hL₀, Category.assoc, Category.assoc, key, ← Category.assoc TG, hTG]

/-- The algebra of the right-hand side of `gradedPiecePlusShift_comm`. -/
lemma bridgeR_paste {V : Type*} [Category* V] {P Q R S U W : V} (R₀ : P ⟶ S) (G : P ⟶ Q)
    (Ci : Q ⟶ R) (Fs : R ⟶ S) (Dd : S ⟶ U) (Dd' : R ⟶ W) (Fs' : W ⟶ U) (Si : Q ⟶ W)
    (hR₀ : R₀ = G ≫ Ci ≫ Fs) (nat : Fs ≫ Dd = Dd' ≫ Fs') (hCi : Ci ≫ Dd' = Si) :
    R₀ ≫ Dd = G ≫ Si ≫ Fs' :=
  bridgeL_paste _ _ _ _ _ _ _ _ hR₀ nat hCi

/-- Two morphisms agree when their images under a faithful functor agree after an
isomorphism. -/
lemma eq_of_map_comp_iso {V W : Type*} [Category* V] [Category* W] (F : V ⥤ W) [F.Faithful]
    {P Q : V} {Z : W} {f g : P ⟶ Q} (e : F.obj Q ≅ Z) (h : F.map f ≫ e.hom = F.map g ≫ e.hom) :
    f = g :=
  F.map_injective ((cancel_mono e.hom).1 h)

/-- `x` is the inverse of `s` read through `c`, when `y` is `c` followed by `s` and `x` is a
section of `y`. -/
lemma inv_comp_paste {V : Type*} [Category* V] {P Q R : V} (x : P ⟶ Q) (y : Q ⟶ P) (c : Q ⟶ R)
    (s : R ≅ P) (hxy : x ≫ y = 𝟙 P) (e : y = c ≫ s.hom) : x ≫ c = s.inv := by
  rw [← cancel_mono s.hom, Category.assoc, ← e, hxy, s.inv_hom_id]

/-- The comparison of the single functors on bounded below complexes with the shift, inverted and
read through the inclusion of all complexes. -/
lemma ι_map_cplusSingleFunctors_shiftIso_inv_app {V : Type*} [Category* V] [Abelian V]
    (n a a' : ℤ) (h : n + a = a') (Z : V) :
    (CochainComplex.Plus.ι V).map
        (((Stacks.DerivedIndexing.cplusSingleFunctors V).shiftIso n a a' h).inv.app Z) ≫
      ((CochainComplex.Plus.ι V).commShiftIso n).hom.app
        ((Stacks.DerivedIndexing.singlePlusFunctor V a').obj Z) =
      ((CochainComplex.singleFunctors V).shiftIso n a a' h).inv.app Z :=
  inv_comp_paste _ _ _ (((CochainComplex.singleFunctors V).shiftIso n a a' h).app Z)
    ((Functor.map_comp _ _ _).symm.trans ((congrArg (CochainComplex.Plus.ι V).map
      (Iso.inv_hom_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))
    (Stacks.DerivedIndexing.ι_map_cplusSingleFunctors_shiftIso_hom_app n a a' h Z)

/-- The commutation with the shift of the functor induced on bounded below complexes, read
through the inclusion of all complexes. -/
lemma ι_map_mapCochainComplexPlus_commShiftIso_hom_app {V W : Type*} [Category* V] [Category* W]
    [Abelian V] [Abelian W] (P : V ⥤ W) [P.Additive] (n : ℤ) (K : CochainComplex.Plus V) :
    (CochainComplex.Plus.ι W).map ((P.mapCochainComplexPlus.commShiftIso n).hom.app K) ≫
      ((CochainComplex.Plus.ι W).commShiftIso n).hom.app (P.mapCochainComplexPlus.obj K) =
      (P.mapHomologicalComplex _).map (((CochainComplex.Plus.ι V).commShiftIso n).hom.app K) ≫
        ((P.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
          ((CochainComplex.Plus.ι V).obj K) := by
  have : NatTrans.CommShift P.mapCochainComplexPlusCompι.hom ℤ :=
    Functor.CommShift.ofComp_compatibility _ _
  have h := NatTrans.shift_app_comm P.mapCochainComplexPlusCompι.hom n K
  rw [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_comp_hom_app] at h
  simp only [Functor.mapCochainComplexPlusCompι, Iso.refl_hom, NatTrans.id_app] at h
  exact (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
    (CategoryTheory.Functor.map_id _ _).symm).trans (h.trans (Category.id_comp _)))

/-- The forward identification `extendXIso` of a term of an extended complex is an `eqToHom`. -/
lemma exists_eqToHom_extendXIso_hom {V : Type*} [Category* V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex V c)
    (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') :
    ∃ h', (K.extendXIso e h).hom = eqToHom h' := by
  unfold HomologicalComplex.extendXIso HomologicalComplex.extend.XIso
  exact ⟨_, eqToIso.hom _⟩

/-- The inverse identification `extendXIso` of a term of an extended complex is an `eqToHom`. -/
lemma exists_eqToHom_extendXIso_inv {V : Type*} [Category* V] [HasZeroMorphisms V] [HasZeroObject V]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex V c)
    (e : c.Embedding c') {i : ι} {i' : ι'} (h : e.f i = i') :
    ∃ h', (K.extendXIso e h).inv = eqToHom h' := by
  unfold HomologicalComplex.extendXIso HomologicalComplex.extend.XIso
  exact ⟨_, eqToIso.inv _⟩

/-- If the degree `k` component of a morphism of complexes is an `eqToHom`, so is its degree `j`
component for `j = k`. -/
lemma exists_eqToHom_f_of_eq {V : Type*} [Category* V] [HasZeroMorphisms V]
    {K L : CochainComplex V ℤ} (f : K ⟶ L) (j k : ℤ) (hj : j = k)
    (h : ∃ h, f.f k = eqToHom h) : ∃ h, f.f j = eqToHom h := by
  subst hj
  exact h

/-- The components of the comparison of an extension with the termwise image are identifications
of objects. -/
lemma exists_eqToHom_modulePlusIso_f {K : CochainComplex
      (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} A)) ℕ} (n : ℕ) :
    ∃ h, ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map (modulePlusIso K).hom).f (n : ℤ) =
      eqToHom h := by
  show ∃ h, (HomologicalComplex.mapHomologicalComplexExtendIso
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) K embeddingUpNat).hom.f (n : ℤ) = _
  rw [HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ embeddingUpNat (i := n)
    (i' := (n : ℤ)) rfl]
  refine exists_eqToHom_comp ?_ ?_
  · exact exists_eqToHom_extendXIso_hom
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex _ |>.obj K)
      embeddingUpNat _
  · exact exists_eqToHom_map (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A))
      (exists_eqToHom_extendXIso_inv K embeddingUpNat _)

/-- The degree `k` component of `gradedPiecePlusIso B D k`, read in all complexes, is
an `eqToHom`. -/
lemma exists_eqToHom_gradedPiecePlusIso_f (k : ℕ) :
    ∃ h, ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map (gradedPiecePlusIso B D k).hom).f
      (k : ℤ) = eqToHom h := by
  show ∃ h, (gradedPieceComplexHom B D k).f (k : ℤ) = _
  rw [gradedPieceComplexHom_f]
  refine exists_eqToHom_comp ?_ (exists_eqToHom_comp ?_ (exists_eqToHom_comp ?_ ?_))
  · exact exists_eqToHom_extendXIso_hom
      ((abelianisationFunctor (A := A)).obj (deRhamGradedPiece B D k)) embeddingUpNat _
  · exact exists_eqToHom_map (_root_.SheafOfModules.toSheaf.{u, u, u, u} (underlyingRingSheaf A))
      (exists_eqToHom_singleObjXSelf_hom (c := ComplexShape.up ℕ) k ((deRhamComplex B D).X k))
  · exact exists_eqToHom_extendXIso_inv (deRhamAbelianComplex B D) embeddingUpNat rfl
  · exact exists_eqToHom_singleObjXSelf_inv _ _

/-- The degree `0` component of `hodgeSinglePlusIso B D k`, read in all complexes, is
an `eqToHom`. -/
lemma exists_eqToHom_hodgeSinglePlusIso_f (k : ℕ) :
    ∃ h, ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map (hodgeSinglePlusIso B D k).hom).f 0 =
      eqToHom h := by
  refine exists_eqToHom_comp ?_ ?_
  · refine exists_eqToHom_of_eq (HomologicalComplex.extendSingleIso_inv_f embeddingUpNat _ 0 0 _) ?_
    refine exists_eqToHom_comp ?_ (exists_eqToHom_comp ?_ ?_)
    · exact exists_eqToHom_singleObjXSelf_hom _ _
    · exact exists_eqToHom_singleObjXSelf_inv _ _
    · exact exists_eqToHom_extendXIso_inv _ embeddingUpNat _
  · refine exists_eqToHom_of_eq (HomologicalComplex.extendMap_f _ embeddingUpNat (i := 0) (i' := 0)
      rfl) ?_
    refine exists_eqToHom_comp ?_ (exists_eqToHom_comp ?_ ?_)
    · exact exists_eqToHom_extendXIso_hom _ embeddingUpNat _
    · refine exists_eqToHom_of_eq
        (HomologicalComplex.singleMapHomologicalComplex_inv_app_self _ _ _ _) ?_
      refine exists_eqToHom_comp ?_ ?_
      · exact exists_eqToHom_singleObjXSelf_hom _ _
      · exact exists_eqToHom_map (_root_.SheafOfModules.toSheaf.{u, u, u, u}
          (underlyingRingSheaf A))
          (exists_eqToHom_singleObjXSelf_inv (c := ComplexShape.up ℕ) 0 ((deRhamComplex B D).X k))
    · exact exists_eqToHom_extendXIso_inv _ embeddingUpNat _

/-- `Ω^a[-a] ⟶ Ω^a[0][-a]` as a morphism of bounded below complexes of modules over the structure
sheaf of `(X, A)`: `gradedPieceShiftIso` read through the identification of the two shifts. -/
def gradedPiecePlusShift (a : ℕ) :
    moduleComplexPlus (X := X) (A := A) (deRhamGradedPiece (X := X) (A := A) (φ := φ) B D a) ⟶
      (CategoryTheory.shiftFunctor (CochainComplex.Plus
        (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))) (-(a : ℤ))).obj
        (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a)) :=
  (CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
      (structureSheafRing (baseRingedSpace A)))).preimage ((gradedPieceShiftIso B D a).hom ≫
    (shiftBridge (S := baseRingedSpace A)
      ((hodgeSingle (X := X) (A := A) (φ := φ) B D a).extend embeddingUpNat) (-(a : ℤ))).hom ≫
        ((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
        (structureSheafRing (baseRingedSpace A)))).commShiftIso (-(a : ℤ))).inv.app
        (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a)))

/-- **The two presentations of `Ω^a[-a]` agree through the shift**, as bounded below complexes of
abelian sheaves. -/
theorem gradedPiecePlusShift_comm (a : ℕ) :
    (modulePlusIso (deRhamGradedPiece B D a)).hom ≫
      (_root_.SheafOfModules.toSheaf (structureSheafRing
      (baseRingedSpace A))).mapCochainComplexPlus.map (gradedPiecePlusShift B D a) ≫
        ((_root_.SheafOfModules.toSheaf (structureSheafRing
          (baseRingedSpace A))).mapCochainComplexPlus.commShiftIso (-(a : ℤ))).hom.app
          (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a)) =
      (gradedPiecePlusIso B D a).hom ≫
        ((Stacks.DerivedIndexing.cplusSingleFunctors (AbelianSheaf X.carrier)).shiftIso
          (-(a : ℤ)) (a : ℤ) 0 (by omega)).inv.app ((deRhamAbelianComplexInt B D).X (a : ℤ)) ≫
        (CategoryTheory.shiftFunctor (CochainComplex.Plus (AbelianSheaf X.carrier)) (-(a : ℤ))).map
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
            (deRhamAbelianIntXIsoNat B D a).hom ≫ (hodgeSinglePlusIso B D a).hom ≫
            (modulePlusIso (hodgeSingle B D a)).hom) := by
  refine eq_of_map_comp_iso (CochainComplex.Plus.ι (AbelianSheaf X.carrier))
    (((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).commShiftIso (-(a : ℤ))).app
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
      (baseRingedSpace A))).mapCochainComplexPlus.obj
      (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a)))) ?_
  have hTG : (CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
      (baseRingedSpace A))).mapCochainComplexPlus.map (gradedPiecePlusShift B D a)) ≫
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (baseRingedSpace A))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((CochainComplex.Plus.ι (_root_.SheafOfModules.{u}
        (structureSheafRing (baseRingedSpace A)))).commShiftIso (-(a : ℤ))).hom.app
        (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))) =
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (baseRingedSpace A))).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((gradedPieceShiftIso B D a).hom ≫ (shiftBridge (S := baseRingedSpace A)
        ((hodgeSingle (X := X) (A := A) (φ := φ) B D a).extend embeddingUpNat) (-(a : ℤ))).hom) :=
    (((_root_.SheafOfModules.toSheaf (structureSheafRing (baseRingedSpace A))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      (congrArg ((_root_.SheafOfModules.toSheaf
      (structureSheafRing (baseRingedSpace A))).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (map_preimage_comp_hom (CochainComplex.Plus.ι
        (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A)))) _ _ _ _
        (Iso.inv_hom_id_app _ _)))
  have eL := bridgeL_paste
    ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      ((modulePlusIso (deRhamGradedPiece B D a)).hom ≫
      (_root_.SheafOfModules.toSheaf (structureSheafRing
      (baseRingedSpace A))).mapCochainComplexPlus.map (gradedPiecePlusShift B D a) ≫
      ((_root_.SheafOfModules.toSheaf (structureSheafRing
        (baseRingedSpace A))).mapCochainComplexPlus.commShiftIso (-(a : ℤ))).hom.app
        (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))))
    ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      (modulePlusIso (deRhamGradedPiece B D a)).hom) _ _ _ _ _ _
    (((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_comp _ _).trans
      (whisker_eq _ ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_comp _ _)))
    (ι_map_mapCochainComplexPlus_commShiftIso_hom_app
      (_root_.SheafOfModules.toSheaf (structureSheafRing (baseRingedSpace A)))
      (-(a : ℤ)) (moduleComplexPlus (X := X) (A := A)
        (hodgeSingle (X := X) (A := A) (φ := φ) B D a))) hTG
  have eR := bridgeR_paste
    ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map ((gradedPiecePlusIso B D a).hom ≫
      ((Stacks.DerivedIndexing.cplusSingleFunctors (AbelianSheaf X.carrier)).shiftIso
      (-(a : ℤ)) (a : ℤ) 0
      (by omega)).inv.app ((deRhamAbelianComplexInt B D).X (a : ℤ)) ≫
        (CategoryTheory.shiftFunctor (CochainComplex.Plus (AbelianSheaf X.carrier)) (-(a : ℤ))).map
        ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
        (deRhamAbelianIntXIsoNat B D a).hom ≫ (hodgeSinglePlusIso B D a).hom ≫
        (modulePlusIso (hodgeSingle B D a)).hom)))
    ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      (gradedPiecePlusIso B D a).hom) _ _ _ _ _ _
    (((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_comp _ _).trans
      (whisker_eq _ ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map_comp _ _)))
    ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).commShiftIso_hom_naturality
      ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
      (deRhamAbelianIntXIsoNat B D a).hom ≫ (hodgeSinglePlusIso B D a).hom ≫
      (modulePlusIso (hodgeSingle B D a)).hom) (-(a : ℤ)))
    (ι_map_cplusSingleFunctors_shiftIso_inv_app (-(a : ℤ)) (a : ℤ) 0 (by omega)
      ((deRhamAbelianComplexInt B D).X (a : ℤ)))
  refine eL.trans (Eq.trans ?_ eR.symm)
  refine HomologicalComplex.Hom.ext (funext fun d => ?_)
  by_cases hd : d = (a : ℤ)
  swap
  · exact (isZero_gradedPieceAbelian_X B D a d hd).eq_of_src _ _
  subst hd
  refine eq_of_exists_eqToHom ?_ ?_
  · refine exists_eqToHom_comp (exists_eqToHom_modulePlusIso_f a) (exists_eqToHom_comp ?_ ?_)
    · refine exists_eqToHom_map (_root_.SheafOfModules.toSheaf
        (structureSheafRing (baseRingedSpace A)))
        (exists_eqToHom_comp (gradedPieceShiftIso_hom_f B D a)
        ⟨rfl, ?_⟩)
      exact (shiftBridge_hom_f _ _ _).trans (eqToHom_refl _ _).symm
    · exact ⟨rfl, (eqToHom_refl _ _).symm⟩
  · refine exists_eqToHom_comp (exists_eqToHom_gradedPiecePlusIso_f B D a)
      (exists_eqToHom_comp ⟨_, singleFunctors_shiftIso_inv_app_f _ _ _ _ _ _
        ((HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) (a : ℤ) _).trans (by
          show _ = ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            ((deRhamAbelianComplexInt B D).X (a : ℤ))).X ((a : ℤ) + -(a : ℤ))
          rw [add_neg_cancel]
          exact (HomologicalComplex.single_obj_X_self (ComplexShape.up ℤ) 0 _).symm))⟩ ?_)
    refine exists_eqToHom_of_eq (CochainComplex.shiftFunctor_map_f'
      (C := AbelianSheaf X.carrier) _ _ _) ?_
    refine exists_eqToHom_f_of_eq (V := AbelianSheaf X.carrier)
      ((CochainComplex.Plus.ι (AbelianSheaf X.carrier)).map
      ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
      (deRhamAbelianIntXIsoNat B D a).hom ≫ (hodgeSinglePlusIso B D a).hom ≫
      (modulePlusIso (hodgeSingle B D a)).hom))
      ((a : ℤ) + -(a : ℤ)) 0 (by omega) ?_
    refine exists_eqToHom_comp ?_ (exists_eqToHom_comp (exists_eqToHom_hodgeSinglePlusIso_f B D a)
      (exists_eqToHom_modulePlusIso_f 0))
    refine exists_eqToHom_of_eq (HomologicalComplex.single_map_f_self _ _ _) ?_
    refine exists_eqToHom_comp ?_ (exists_eqToHom_comp ?_ ?_)
    · exact exists_eqToHom_singleObjXSelf_hom _ _
    · exact exists_eqToHom_extendXIso_hom (deRhamAbelianComplex B D) embeddingUpNat rfl
    · exact exists_eqToHom_singleObjXSelf_inv _ _

end Bridge

/-! ### The identification of a single complex in degree `q` through the shift -/

section SingleShift

variable {V W : Type*} [Category* V] [Category* W] [Abelian V] [Abelian W] [HasDerivedCategory V]
  [HasDerivedCategory W]

/-- The inverse of `e = c⁻¹ ≫ m` is `m' ≫ c` when `m'` is a section of `m`. -/
lemma inv_eq_of_hom_paste {V : Type*} [Category* V] {P Q R : V} (e : P ≅ R) (c : Q ≅ P)
    (m : Q ⟶ R) (m' : R ⟶ Q) (he : e.hom = c.inv ≫ m) (hm : m ≫ m' = 𝟙 Q) :
    e.inv = m' ≫ c.hom := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id, he, Category.assoc, ← Category.assoc m, hm,
    Category.id_comp, Iso.inv_hom_id]

/-- The comparison of the single functors into `D⁺` with the shift, inverted: the localization of
the comparison on bounded below complexes, followed by the commutation of the localization with
the shift. -/
lemma plusSingleFunctors_shiftIso_inv_app (n a a' : ℤ) (h : n + a = a') (Z : V) :
    ((DerivedCategory.Plus.singleFunctors V).shiftIso n a a' h).inv.app Z =
      DerivedCategory.Plus.Q.map
          (((Stacks.DerivedIndexing.cplusSingleFunctors V).shiftIso n a a' h).inv.app Z) ≫
        (DerivedCategory.Plus.Q.commShiftIso n).hom.app
          ((Stacks.DerivedIndexing.singlePlusFunctor V a').obj Z) :=
  inv_eq_of_hom_paste (((DerivedCategory.Plus.singleFunctors V).shiftIso n a a' h).app Z)
    ((DerivedCategory.Plus.Q.commShiftIso n).app
      ((Stacks.DerivedIndexing.singlePlusFunctor V a').obj Z)) _ _
    (Stacks.DerivedIndexing.plusSingleFunctors_shiftIso_hom_app n a a' h Z)
    ((DerivedCategory.Plus.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Plus.Q.map
      (Iso.hom_inv_id_app _ _)).trans (CategoryTheory.Functor.map_id _ _)))

/-- **The identification `H^{p + q}(Φ(F[-q])) ≅ H^p(Φ(F))` of
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso` is `shiftHomologyIso`** of the
composite of the localization with `Φ`, read through the comparison of the single functors with
the shift. -/
theorem singleFunctorCompHomologyFunctorShiftIso_app_hom (Φ : DerivedCategory.Plus V ⥤
      DerivedCategory.Plus W) [Φ.CommShift ℤ] (p q : ℤ) (Z : V) :
    ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ p q).app Z).hom =
      (DerivedCategory.Plus.homologyFunctor W (p + q)).map (Φ.map (DerivedCategory.Plus.Q.map
        (((Stacks.DerivedIndexing.cplusSingleFunctors V).shiftIso (-q) q 0 (by omega)).inv.app
          Z))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIso (DerivedCategory.Plus.Q ⋙ Φ)
          ((Stacks.DerivedIndexing.singlePlusFunctor V 0).obj Z) (-q) (p + q) p
            (by omega)).hom := by
  rw [Stacks.Cohomology.RealizationShift.shiftHomologyIso_comp]
  have e : ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso Φ p q).app Z).hom =
      (DerivedCategory.Plus.homologyFunctor W (p + q)).map (Φ.map
          (((DerivedCategory.Plus.singleFunctors V).shiftIso (-q) q 0 (by omega)).inv.app Z)) ≫
        (DerivedCategory.Plus.homologyFunctor W (p + q)).map
          ((Φ.commShiftIso (-q)).hom.app ((DerivedCategory.Plus.singleFunctor V 0).obj Z)) ≫
        ((DerivedCategory.Plus.homologyFunctor W 0).shiftIso (-q) (p + q) p (by omega)).hom.app
          (Φ.obj ((DerivedCategory.Plus.singleFunctor V 0).obj Z)) := by
    simp only [DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso, Iso.app_hom]
    rfl
  rw [e, plusSingleFunctors_shiftIso_inv_app]
  exact (congrArg (· ≫ _) ((congrArg (DerivedCategory.Plus.homologyFunctor W (p + q)).map
    (Φ.map_comp _ _)).trans ((DerivedCategory.Plus.homologyFunctor W (p + q)).map_comp _ _))).trans
    (Category.assoc _ _ _)

end SingleShift

/-! ### The abelian identification of a graded piece through the shift -/

section AbelianShift

/-- A functor preserves an equality of triple composites. -/
lemma map_comp₃_eq {V W : Type*} [Category* V] [Category* W] (G : V ⥤ W) {P Q R S Q' R' : V}
    {a : P ⟶ Q} {b : Q ⟶ R} {c : R ⟶ S} {d : P ⟶ Q'} {e : Q' ⟶ R'} {f : R' ⟶ S}
    (h : a ≫ b ≫ c = d ≫ e ≫ f) : G.map a ≫ G.map b ≫ G.map c = G.map d ≫ G.map e ≫ G.map f := by
  simp only [← Functor.map_comp, h]

/-- The algebra of `gradedPiece_shift_abelian`, with every object and morphism a variable. -/
lemma abelianShift_paste {V : Type*} [Category* V] {P Q R S U W Z₁ Z₂ : V} (G : P ⟶ Q)
    (Ci : Q ⟶ R) (Sx : R ⟶ S) (Pφ : S ⟶ U) (Fsh : R ⟶ W) (Sy : W ⟶ U) (M : P ⟶ Z₁)
    (Tθ : Z₁ ⟶ Z₂) (Cs : Z₂ ⟶ W) (Sf : Z₂ ⟶ U) (nat : Fsh ≫ Sy = Sx ≫ Pφ)
    (chain : M ≫ Tθ ≫ Cs = G ≫ Ci ≫ Fsh) (comp : Sf = Cs ≫ Sy) :
    G ≫ (Ci ≫ Sx) ≫ Pφ = M ≫ Tθ ≫ Sf := by
  rw [comp, Category.assoc, ← nat, ← reassoc_of% chain]

/-- **The abelian identification of a graded piece with a shifted sheaf of forms is
`shiftHomologyIso`**: the identification `H^{i + a}(X, Ω^a[-a]) ≅ H^i(X, Ω^a[0])` of
`DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso`, read through the two
presentations of the graded piece and of `Ω^a[0]`, is the shift identification of the derived
global sections of the underlying complexes of abelian sheaves of the complexes of modules,
read through `gradedPiecePlusShift`. -/
theorem gradedPiece_shift_abelian (a : ℕ) (i : ℤ) :
    (gradedPieceCohomologyIso B D a (i + a)).hom ≫
        ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i + a)).map
          ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          (((Stacks.DerivedIndexing.cplusSingleFunctors (AbelianSheaf X.carrier)).shiftIso
            (-(a : ℤ)) (a : ℤ) 0 (by omega)).inv.app ((deRhamAbelianComplexInt B D).X (a : ℤ))))) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIso (DerivedCategory.Plus.Q ⋙
          (sectionsFunctor (baseRingedSpace A).carrier ⊤).rightDerivedFunctorPlus)
          ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).obj
            ((deRhamAbelianComplexInt B D).X (a : ℤ)))
          (-(a : ℤ)) (i + a) i (by omega)).hom) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
          ((DerivedCategory.Plus.Q ⋙ (sectionsFunctor (baseRingedSpace A).carrier
          ⊤).rightDerivedFunctorPlus).map ((Stacks.DerivedIndexing.singlePlusFunctor
          (AbelianSheaf X.carrier) 0).map (deRhamAbelianIntXIsoNat B D a).hom ≫
          (hodgeSinglePlusIso B D a).hom ≫ (modulePlusIso (hodgeSingle B D a)).hom)) =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i + a)).map
        ((DerivedCategory.Plus.Q ⋙ (sectionsFunctor (baseRingedSpace A).carrier
        ⊤).rightDerivedFunctorPlus).map (modulePlusIso (deRhamGradedPiece B D a)).hom) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i + a)).map
          (((_root_.SheafOfModules.toSheaf (structureSheafRing
          (baseRingedSpace A))).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙
          (sectionsFunctor (baseRingedSpace A).carrier ⊤).rightDerivedFunctorPlus).map
          (gradedPiecePlusShift B D a)) ≫
        (Stacks.Cohomology.RealizationShift.shiftHomologyIso
          ((_root_.SheafOfModules.toSheaf (structureSheafRing
          (baseRingedSpace A))).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ⋙
          (sectionsFunctor (baseRingedSpace A).carrier ⊤).rightDerivedFunctorPlus)
          (moduleComplexPlus (X := X) (A := A) (hodgeSingle (X := X) (A := A) (φ := φ) B D a))
          (-(a : ℤ)) (i + a) i
          (by omega)).hom := by
  have chain := map_comp₃_eq ((DerivedCategory.Plus.Q ⋙
      (sectionsFunctor (baseRingedSpace A).carrier ⊤).rightDerivedFunctorPlus) ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (i + a))
      (gradedPiecePlusShift_comm B D a)
  exact abelianShift_paste _ _ _ _ _ _ _ _ _ _
    (Stacks.Cohomology.RealizationShift.shiftHomologyIso_naturality (DerivedCategory.Plus.Q ⋙
      (sectionsFunctor (baseRingedSpace A).carrier ⊤).rightDerivedFunctorPlus)
      ((Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X.carrier) 0).map
      (deRhamAbelianIntXIsoNat B D a).hom ≫ (hodgeSinglePlusIso B D a).hom ≫
      (modulePlusIso (hodgeSingle B D a)).hom) (-(a : ℤ)) (i + a) i
      (by omega)) chain
    (Stacks.Cohomology.RealizationShift.shiftHomologyIso_comp
      (_root_.SheafOfModules.toSheaf (structureSheafRing (baseRingedSpace A))).mapCochainComplexPlus
      (DerivedCategory.Plus.Q ⋙ (sectionsFunctor (baseRingedSpace A).carrier
      ⊤).rightDerivedFunctorPlus) (moduleComplexPlus (X := X) (A := A)
      (hodgeSingle (X := X) (A := A) (φ := φ) B D a)) (-(a : ℤ)) (i + a) i
      (by omega))

end AbelianShift

end AlgebraicGeometry.SheafOfModules

end
