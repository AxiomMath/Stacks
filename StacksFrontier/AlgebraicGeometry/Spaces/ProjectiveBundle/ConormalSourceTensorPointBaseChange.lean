module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceTensorBaseChange

/-!
# Tensor products, Stacks 03LU and the Zariski reading

Let `x : T ⟶ X` be a scheme point of an algebraic space and `h : T' ⟶ T` a morphism of test
objects.  This file records, in the spellings used when the point readings `R_T ∘ x^*` are
compared along `h`, the inputs of the monoidality of that comparison: Stacks 03LU is monoidal
(Stacks 03EL) after the Zariski reading, the Zariski reading tensor isomorphism is natural in
the tensor product sheaf of the structure presheaf, and the two tensor comparisons of a point
reading (through the monoidal tensor product and through the tensor product sheaf) agree.

## Main results

* `AlgebraicGeometry.Space.zariskiReading_map_modulePullbackCompIso_hom_app_tensor`: Stacks 03LU
  is monoidal, read on a represented space.
* `AlgebraicGeometry.Space.zariskiReadingTensorObjIso_hom_naturality_sheafTensor` and
  `AlgebraicGeometry.Space.zariskiReadingTensorObjIso_bifunctorNaturalitySquare`: naturality of
  the Zariski reading tensor isomorphism in the tensor product sheaf of the structure presheaf.
* `AlgebraicGeometry.Space.zariskiReading_mapIso_modulePullbackTensorIso_trans`: the Zariski
  reading of Stacks 03EL in the monoidal spelling, followed by `zariskiReadingTensorObjIso`, is
  the Zariski reading of `Stacks.SheafOfModules.pullbackTensorIso` followed by
  `zariskiReadingTensorIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03LU is monoidal**, read on a represented space: the composition comparison
`f^*g^* ≅ (g ∘ f)^*` intertwines Stacks 03EL for `f`, `g` and `g ∘ f`, after the Zariski
reading. -/
theorem zariskiReading_map_modulePullbackCompIso_hom_app_tensor {T' : BigFppfOver B S hS}
    {Y Z : AlgebraicSpaces B S hS}
    (f : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (g : Y ⟶ Z) (F G : Modules.{u, u} B S hS Z.1 Z.2) :
    @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj (F ⊗ G))) _
        ((modulePullbackCompIso B S hS f g).hom.app (F ⊗ G)) ≫
      @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _
        (modulePullbackTensorIso B S hS (f ≫ g) F G).hom =
      @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _
        ((modulePullback B S hS f).map (modulePullbackTensorIso B S hS g F G).hom) ≫
      @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _
        (modulePullbackTensorIso B S hS f _ _).hom ≫
      @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _
        (MonoidalCategory.tensorHom
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullbackCompIso B S hS f g).hom.app F)
          ((modulePullbackCompIso B S hS f g).hom.app G)) :=
  ((zariskiReadingFunctor T').map_comp _ _).symm.trans
    ((congrArg (zariskiReadingFunctor T').map
      (modulePullbackCompIso_hom_app_tensor B S hS f g F G)).trans
      (((zariskiReadingFunctor T').map_comp _ _).trans
        (congrArg (_ ≫ ·) ((zariskiReadingFunctor T').map_comp _ _))))

/-- Naturality of `zariskiReadingTensorObjIso`, read in the tensor product sheaf of the structure
presheaf through `monoidalTensorSheafTensorIso`. -/
theorem zariskiReadingTensorObjIso_hom_naturality_sheafTensor (T' : BigFppfOver B S hS)
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    @CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _
        (MonoidalCategory.tensorHom
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) a b) ≫
      (zariskiReadingTensorObjIso T' P' Q' hP' hQ').hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj P') ((zariskiReadingFunctor T').obj Q')).hom =
      ((zariskiReadingTensorObjIso T' P Q hP hQ).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj P) ((zariskiReadingFunctor T').obj Q)).hom) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
              (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).map
          (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _ a)).app
          ((zariskiReadingFunctor T').obj Q) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
              (forget₂ CommRingCat RingCat)
              ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩).obj
          ((zariskiReadingFunctor T').obj P')).map
          (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
            Scheme.Modules.instCategory (zariskiReadingFunctor T') _ _ b) :=
  monoidalTensorSheafTensorIso_naturality _ _ _ _ _ _
    (zariskiReadingTensorObjIso_hom_naturality T' a b hP hQ hP' hQ')

/-- The square `R'(d) ≫ Z'' = Z' ≫ F(a', b')` of a naturality of a tensor comparison `Z`, as a
proposition. -/
abbrev _root_.CategoryTheory.Functor.BifunctorNaturalitySquare {𝒜 ℬ : Type*} [Category 𝒜]
    [iℬ : Category ℬ] (R' : 𝒜 ⥤ ℬ) (F : ℬ ⥤ ℬ ⥤ ℬ) {E' E'' : 𝒜} {W₁ W₂ V₁ V₂ : ℬ} (d : E' ⟶ E'')
    (Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂) (a' : W₁ ⟶ V₁) (b' : W₂ ⟶ V₂)
    (Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂) : Prop :=
  R'.map d ≫ Z'' = Z' ≫ ((F.map a').app W₂ ≫ (F.obj V₁).map b')

/-- `zariskiReadingTensorObjIso_hom_naturality_sheafTensor` as a
`CategoryTheory.Functor.BifunctorNaturalitySquare` for the modules on the scheme. -/
theorem zariskiReadingTensorObjIso_bifunctorNaturalitySquare (T' : BigFppfOver B S hS)
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    CategoryTheory.Functor.BifunctorNaturalitySquare
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
          Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
            (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (E' := MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) P Q)
      (E'' := MonoidalCategory.tensorObj
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) P' Q')
      (W₁ := (zariskiReadingFunctor T').obj P) (W₂ := (zariskiReadingFunctor T').obj Q)
      (V₁ := (zariskiReadingFunctor T').obj P') (V₂ := (zariskiReadingFunctor T').obj Q')
      (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) a b)
      ((zariskiReadingTensorObjIso T' P Q hP hQ).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj P) ((zariskiReadingFunctor T').obj Q)).hom)
      ((zariskiReadingFunctor T').map a) ((zariskiReadingFunctor T').map b)
      ((zariskiReadingTensorObjIso T' P' Q' hP' hQ').hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj P') ((zariskiReadingFunctor T').obj Q')).hom) :=
  zariskiReadingTensorObjIso_hom_naturality_sheafTensor T' a b hP hQ hP' hQ'

/-- A functor carries `u ≪≫ v ≪≫ w⁻¹` followed by `w` to `u ≪≫ v`. -/
theorem _root_.CategoryTheory.Functor.mapIso_trans_symm_trans_mapIso_trans {𝒞 𝒟 : Type*}
    [Category 𝒞] [Category 𝒟] (R : 𝒞 ⥤ 𝒟) {a b c d : 𝒞} {e : 𝒟} (u : a ≅ b) (v : b ≅ c)
    (w : d ≅ c) (Z : R.obj c ≅ e) :
    R.mapIso (u ≪≫ v ≪≫ w.symm) ≪≫ R.mapIso w ≪≫ Z = R.mapIso (u ≪≫ v) ≪≫ Z := by
  ext
  simp

/-- **The two tensor comparisons of a point reading agree**: the Zariski reading of Stacks 03EL
in the monoidal spelling followed by `zariskiReadingTensorObjIso` is the Zariski reading of the
tensor comparison `Stacks.SheafOfModules.pullbackTensorIso` followed by
`zariskiReadingTensorIso`. -/
theorem zariskiReading_mapIso_modulePullbackTensorIso_trans {T : BigFppfOver B S hS}
    {Y : AlgebraicSpaces B S hS} (f : schemeSpace T ⟶ Y)
    (F G : Modules.{u, u} B S hS Y.1 Y.2)
    (hF : ((modulePullback B S hS f).obj F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS f).obj G).IsQuasicoherentOnSite) :
    (zariskiReadingFunctor T).mapIso (modulePullbackTensorIso B S hS f F G) ≪≫
        zariskiReadingTensorObjIso T _ _ hF hG =
      (zariskiReadingFunctor T).mapIso ((modulePullback B S hS f).mapIso
          (modulesTensorObjIso B S hS Y.1 Y.2 F G) ≪≫
        modulePullbackTensorComparison f G F) ≪≫
        zariskiReadingTensorIso T _ _ hF hG := by
  unfold zariskiReadingTensorObjIso modulePullbackTensorIso modulePullbackTensorComparison
  exact CategoryTheory.Functor.mapIso_trans_symm_trans_mapIso_trans _ _ _ _ _

end AlgebraicGeometry.Space

end
