module

public import
    StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourceTensorPointBaseChange

/-!
# Monoidality of the identification of the point readings

Let `x : T ⟶ X` be a scheme point of an algebraic space, `h : T' ⟶ T` a morphism of test
objects, `τ` the morphism of schemes underlying `h` and `φ` the morphism of represented algebraic
spaces.  The identification `τ^* ρ_x ⟶ ρ_{x ∘ h}` of the point readings `ρ = R ∘ (-)^*`, made of
the base change of the Zariski reading and Stacks 03LU, is monoidal (for Stacks 01CD on the
scheme side and Stacks 03EL on the space side) as soon as the base change of the Zariski reading
is.  The squares are stated through named propositions which fix the category in which each
composite is taken: the modules on `T'` for every morphism of sheaves on `T'`.

## Main results

* `AlgebraicGeometry.Space.ZariskiReadingPullbackTensorSquare`: the monoidality of the base
  change of the Zariski reading on quasi-coherent modules, as a proposition.
* `CategoryTheory.Functor.tensorPasteConclusion_of_squares`: the paste of the four squares.
* `AlgebraicGeometry.Space.pointReadingBaseChange_tensor_of`: the identification of the point
  readings is monoidal, given the monoidality of the base change of the Zariski reading.
* `AlgebraicGeometry.Space.zariskiReadingPullbackHom_tensorPasteNaturality` and
  `AlgebraicGeometry.Space.modulePullbackCompIso_tensorPasteMiddle_point`: two of the squares at a
  scheme point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

/-- The upper square `P(Z) ≫ κ ≫ F(a, b) = θ' ≫ R'(mφ) ≫ Z'` of
`CategoryTheory.Functor.bifunctor_tensor_paste_of_map`, as a proposition. -/
abbrev _root_.CategoryTheory.Functor.TensorPasteUpper {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ)
    (F : ℬ ⥤ ℬ ⥤ ℬ) {D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ : ℬ} {GD' E' : 𝒜}
    (Z : R.obj D' ⟶ C') (κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂) (a : Y₁ ⟶ W₁) (b : Y₂ ⟶ W₂)
    (θ' : P.obj (R.obj D') ⟶ R'.obj GD') (mφ : GD' ⟶ E') (Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂) :
    Prop :=
  P.map Z ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = θ' ≫ R'.map mφ ≫ Z'

/-- The naturality square `P(R(m)) ≫ θ' = θ ≫ R'(gm)` of
`CategoryTheory.Functor.bifunctor_tensor_paste_of_map`, as a proposition. -/
abbrev _root_.CategoryTheory.Functor.TensorPasteNaturality {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ)
    {D D' : 𝒟} {GD GD' : 𝒜} (m : D ⟶ D') (θ' : P.obj (R.obj D') ⟶ R'.obj GD')
    (θ : P.obj (R.obj D) ⟶ R'.obj GD) (gm : GD ⟶ GD') : Prop :=
  P.map (R.map m) ≫ θ' = θ ≫ R'.map gm

/-- The middle square `R'(c) ≫ R'(m') = R'(gm) ≫ R'(mφ) ≫ R'(d)` of
`CategoryTheory.Functor.bifunctor_tensor_paste_of_map_map`, as a proposition. -/
abbrev _root_.CategoryTheory.Functor.TensorPasteMiddle {𝒜 ℬ : Type*} [Category 𝒜]
    [iℬ : Category ℬ] (R' : 𝒜 ⥤ ℬ) {GD GD' E' E'' Ex : 𝒜} (c : GD ⟶ Ex) (m' : Ex ⟶ E'')
    (gm : GD ⟶ GD') (mφ : GD' ⟶ E') (d : E' ⟶ E'') : Prop :=
  R'.map c ≫ R'.map m' = R'.map gm ≫ R'.map mφ ≫ R'.map d

/-- The conclusion of `CategoryTheory.Functor.bifunctor_tensor_paste_of_map`, as a
proposition. -/
abbrev _root_.CategoryTheory.Functor.TensorPasteConclusion {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞) (R' : 𝒜 ⥤ ℬ)
    (F : ℬ ⥤ ℬ ⥤ ℬ) {D D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ} {GD E'' Ex : 𝒜}
    (m : D ⟶ D') (Z : R.obj D' ⟶ C') (κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂) (a : Y₁ ⟶ W₁)
    (a' : W₁ ⟶ V₁) (b : Y₂ ⟶ W₂) (b' : W₂ ⟶ V₂) (θ : P.obj (R.obj D) ⟶ R'.obj GD)
    (c : GD ⟶ Ex) (m' : Ex ⟶ E'') (Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂) : Prop :=
  P.map (R.map m ≫ Z) ≫ κ ≫ ((F.map (a ≫ a')).app Y₂ ≫ (F.obj V₁).map (b ≫ b')) =
    θ ≫ R'.map c ≫ R'.map m' ≫ Z''

/-- `CategoryTheory.Functor.bifunctor_tensor_paste_of_map_map` with its squares and its
conclusion stated through the named propositions. -/
theorem _root_.CategoryTheory.Functor.tensorPasteConclusion_of_squares {𝒜 ℬ 𝒞 𝒟 : Type*}
    [Category 𝒜] [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] (P : 𝒞 ⥤ ℬ) (R : 𝒟 ⥤ 𝒞)
    (R' : 𝒜 ⥤ ℬ) (F : ℬ ⥤ ℬ ⥤ ℬ) {D D' : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ V₁ V₂ : ℬ}
    {GD GD' E' E'' Ex : 𝒜}
    {m : D ⟶ D'} {Z : R.obj D' ⟶ C'} {κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂} {a : Y₁ ⟶ W₁}
    {b : Y₂ ⟶ W₂} {θ' : P.obj (R.obj D') ⟶ R'.obj GD'} {gm : GD ⟶ GD'} {mφ : GD' ⟶ E'}
    {Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂} {θ : P.obj (R.obj D) ⟶ R'.obj GD}
    {c : GD ⟶ Ex} {m' : Ex ⟶ E''} {d : E' ⟶ E''} {a' : W₁ ⟶ V₁} {b' : W₂ ⟶ V₂}
    {Z'' : R'.obj E'' ⟶ (F.obj V₁).obj V₂}
    (t : CategoryTheory.Functor.TensorPasteUpper P R R' F Z κ a b θ' mφ Z')
    (n : CategoryTheory.Functor.TensorPasteNaturality P R R' m θ' θ gm)
    (hc : CategoryTheory.Functor.TensorPasteMiddle R' c m' gm mφ d)
    (n' : CategoryTheory.Functor.BifunctorNaturalitySquare R' F d Z' a' b' Z'') :
    CategoryTheory.Functor.TensorPasteConclusion P R R' F m Z κ a a' b b' θ c m' Z'' :=
  CategoryTheory.Functor.bifunctor_tensor_paste_of_map_map P R R' F m Z κ a b θ' gm mφ Z' θ c m' d
    a' b' Z'' t n hc n'

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The base change of the Zariski reading is monoidal on quasi-coherent modules**, as the
upper square of `CategoryTheory.Functor.bifunctor_tensor_paste_of_map_map`: `τ^*` of the Zariski
reading tensor isomorphism followed by Stacks 01CD and the base change in both factors is the
base change at `𝒩 ⊗ ℳ` followed by Stacks 03EL for `φ` and the Zariski reading tensor
isomorphism.  Every composite of morphisms of sheaves on `T'` is taken in the modules on `T'`. -/
def ZariskiReadingPullbackTensorSquare {T T' : BigFppfOver B S hS} (h : T' ⟶ T) : Prop :=
  ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
    CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' :=
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
          ((zariskiReadingFunctor T).obj (N))).obj
          ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
      ((Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
        ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
      ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
      ((zariskiReadingPullbackHom h).app
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T'
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N)))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))).hom)

/-- Stacks 03LU is monoidal (Stacks 03EL), read on a represented space, as the middle square of
the paste. -/
theorem modulePullbackCompIso_tensorPasteMiddle {T' : BigFppfOver B S hS}
    {Y Z : AlgebraicSpaces B S hS}
    (f : (⟨yoneda.obj T', isAlgebraicSpace_yoneda B S hS T'⟩ : AlgebraicSpaces B S hS) ⟶ Y)
    (g : Y ⟶ Z) (F G : Modules.{u, u} B S hS Z.1 Z.2) :
    CategoryTheory.Functor.TensorPasteMiddle
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (GD := (modulePullback B S hS f).obj ((modulePullback B S hS g).obj (F ⊗ G)))
      (GD' := (modulePullback B S hS f).obj
        ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS Y.1 Y.2)
          ((modulePullback B S hS g).obj (F)) ((modulePullback B S hS g).obj (G)))))
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj (F)))
          ((modulePullback B S hS f).obj ((modulePullback B S hS g).obj (G)))))
      (E'' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS (f ≫ g)).obj (F)) ((modulePullback B S hS (f ≫ g)).obj (G))))
      (Ex := (modulePullback B S hS (f ≫ g)).obj (F ⊗ G))
      (zariskiReadingFunctor T') ((modulePullbackCompIso B S hS f g).hom.app (F ⊗ G))
      (modulePullbackTensorIso B S hS (f ≫ g) F G).hom
      ((modulePullback B S hS f).map (modulePullbackTensorIso B S hS g F G).hom)
      (modulePullbackTensorIso B S hS f _ _).hom
      (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        ((modulePullbackCompIso B S hS f g).hom.app F)
        ((modulePullbackCompIso B S hS f g).hom.app G)) :=
  zariskiReading_map_modulePullbackCompIso_hom_app_tensor f g F G

/-- `zariskiReadingTensorObjIso_bifunctorNaturalitySquare` with the Zariski readings of `a` and
`b` taken in the modules on the scheme. -/
theorem zariskiReadingTensorObjIso_bifunctorNaturalitySquare_modules (T' : BigFppfOver B S hS)
    {P P' Q Q' : Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')}
    (a : P ⟶ P') (b : Q ⟶ Q') (hP : P.IsQuasicoherentOnSite) (hQ : Q.IsQuasicoherentOnSite)
    (hP' : P'.IsQuasicoherentOnSite) (hQ' : Q'.IsQuasicoherentOnSite) :
    CategoryTheory.Functor.BifunctorNaturalitySquare
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) (P) (Q)))
      (E'' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) (P')
          (Q')))
      (W₁ := (zariskiReadingFunctor T').obj (P))
      (W₂ := (zariskiReadingFunctor T').obj (Q))
      (V₁ := (zariskiReadingFunctor T').obj (P'))
      (V₂ := (zariskiReadingFunctor T').obj (Q'))
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')) (a) (b))
      ((zariskiReadingTensorObjIso T' (P) (Q) hP hQ).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj (P)) ((zariskiReadingFunctor T').obj (Q))).hom)
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') (P) (P') (a))
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T') (Q) (Q') (b))
      ((zariskiReadingTensorObjIso T' (P') (Q') hP' hQ').hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj (P')) ((zariskiReadingFunctor T').obj (Q'))).hom) :=
  zariskiReadingTensorObjIso_hom_naturality_sheafTensor T' a b hP hQ hP' hQ'

section Tensor

variable (X : AlgebraicSpaces B S hS) {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1)
  (h : T' ⟶ T)

/-- Naturality of the base change of the Zariski reading at Stacks 03EL for `x`, as the
naturality square of the paste. -/
theorem zariskiReadingPullbackHom_tensorPasteNaturality (A₁ A₂ : Modules.{u, u} B S hS X.1 X.2) :
    CategoryTheory.Functor.TensorPasteNaturality
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D := (modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂)))
      (D' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((modulePullback B S hS (pointHom x)).obj (A₁))
          ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (GD := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂))))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((modulePullback B S hS (pointHom x)).obj (A₁))
          ((modulePullback B S hS (pointHom x)).obj (A₂)))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T')
      (modulePullbackTensorIso B S hS (pointHom x) A₁ A₂).hom
      ((zariskiReadingPullbackHom h).app
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((modulePullback B S hS (pointHom x)).obj (A₁))
          ((modulePullback B S hS (pointHom x)).obj (A₂)))))
      ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂))))
      ((modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackTensorIso B S hS (pointHom x) A₁ A₂).hom) :=
  (zariskiReadingPullbackHom h).naturality _

/-- `modulePullbackCompIso_tensorPasteMiddle` at `φ` and a scheme point `x`, with the objects of
the paste. -/
theorem modulePullbackCompIso_tensorPasteMiddle_point (A₁ A₂ : Modules.{u, u} B S hS X.1 X.2) :
    CategoryTheory.Functor.TensorPasteMiddle
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (GD := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂))))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((modulePullback B S hS (pointHom x)).obj (A₁))
          ((modulePullback B S hS (pointHom x)).obj (A₂)))))
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
            ((modulePullback B S hS (pointHom x)).obj (A₁)))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
            ((modulePullback B S hS (pointHom x)).obj (A₂)))))
      (E'' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))))
      (Ex := (modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj ((A₁ ⊗ A₂)))
      (zariskiReadingFunctor T')
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
        ((A₁ ⊗ A₂)))
      (modulePullbackTensorIso B S hS ((representedSpaceMap B S hS h) ≫ pointHom x) A₁ A₂).hom
      ((modulePullback B S hS (representedSpaceMap B S hS h)).map
        (modulePullbackTensorIso B S hS (pointHom x) A₁ A₂).hom)
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h)
        ((modulePullback B S hS (pointHom x)).obj (A₁))
        ((modulePullback B S hS (pointHom x)).obj (A₂))).hom
      (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₁))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
          (A₂))) := by
  with_reducible_and_instances
    exact modulePullbackCompIso_tensorPasteMiddle (representedSpaceMap B S hS h) (pointHom x) A₁ A₂

/-- `zariskiReadingTensorObjIso_bifunctorNaturalitySquare_modules` at `x^*Aᵢ` and Stacks 03LU, with
the objects of the paste. -/
theorem zariskiReadingTensorObjIso_bifunctorNaturalitySquare_point
    (A₁ A₂ : Modules.{u, u} B S hS X.1 X.2)
    (hA₁ : A₁.IsQuasicoherentOnSite) (hA₂ : A₂.IsQuasicoherentOnSite) :
    CategoryTheory.Functor.BifunctorNaturalitySquare
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
            ((modulePullback B S hS (pointHom x)).obj (A₁)))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
            ((modulePullback B S hS (pointHom x)).obj (A₂)))))
      (E'' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))))
      (W₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₁))))
      (W₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (V₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁)))
      (V₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂)))
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (MonoidalCategory.tensorHom
        (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₁))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₂)))
      ((zariskiReadingTensorObjIso T'
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₁)))
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₂)))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) ((modulePullback B S hS (pointHom x)).obj (A₁))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₁)
            hA₁))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) ((modulePullback B S hS (pointHom x)).obj (A₂))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₂)
            hA₂))).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
              ((modulePullback B S hS (pointHom x)).obj (A₁))))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
              ((modulePullback B S hS (pointHom x)).obj (A₂))))).hom)
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₁)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₁)))
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₂)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₂)))
      ((zariskiReadingTensorObjIso T'
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          ((representedSpaceMap B S hS h) ≫ pointHom x) (A₁) hA₁)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          ((representedSpaceMap B S hS h) ≫ pointHom x) (A₂) hA₂)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁)))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj
              (A₂)))).hom) :=
  zariskiReadingTensorObjIso_bifunctorNaturalitySquare_modules T'
    (P := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
      ((modulePullback B S hS (pointHom x)).obj (A₁)))
    (Q := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
      ((modulePullback B S hS (pointHom x)).obj (A₂)))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₁))
    ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₂))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS h) ((modulePullback B S hS (pointHom x)).obj (A₁))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₁) hA₁))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      (representedSpaceMap B S hS h) ((modulePullback B S hS (pointHom x)).obj (A₂))
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₂) hA₂))
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      ((representedSpaceMap B S hS h) ≫ pointHom x) (A₁) hA₁)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
      ((representedSpaceMap B S hS h) ≫ pointHom x) (A₂) hA₂)

/-- **The identification of the point readings at `x ∘ h` and at `x` is monoidal**, given the
monoidality of the base change of the Zariski reading: `τ^*` of the tensor comparison of `ρ_x`
followed by Stacks 01CD and the identification in both factors is the identification at
`A₁ ⊗ A₂` followed by the tensor comparison of `ρ_{x ∘ h}`. -/
theorem pointReadingBaseChange_tensor_of
    (hc : ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
      (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
      CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' :=
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
          ((zariskiReadingFunctor T).obj (N))).obj
          ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
      ((Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
        ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
      ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
      ((zariskiReadingPullbackHom h).app
        ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T'
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N))
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (N)))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M)))).hom))
    (A₁ A₂ : Modules.{u, u} B S hS X.1 X.2) (hA₁ : A₁.IsQuasicoherentOnSite)
    (hA₂ : A₂.IsQuasicoherentOnSite) :
    CategoryTheory.Functor.TensorPasteConclusion
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D := (modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂)))
      (D' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
          ((modulePullback B S hS (pointHom x)).obj (A₁))
          ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (C' :=
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₁)))).obj
      ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₁))))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (W₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₁))))
      (W₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₂))))
      (V₁ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁)))
      (V₂ := (zariskiReadingFunctor T').obj
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂)))
      (GD := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
        ((modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂))))
      (E'' :=
        (MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T'))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
          ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))))
      (Ex := (modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj ((A₁ ⊗ A₂)))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
      (zariskiReadingFunctor T')
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      (modulePullbackTensorIso B S hS (pointHom x) A₁ A₂).hom
      ((zariskiReadingTensorObjIso T ((modulePullback B S hS (pointHom x)).obj (A₁))
        ((modulePullback B S hS (pointHom x)).obj (A₂))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₁) hA₁)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₂)
          hA₂)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₁)))
          ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₂)))).hom)
      ((Stacks.RingedSpace.comparisonBifunctorIso
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
        ((zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₁)),
          (zariskiReadingFunctor T).obj ((modulePullback B S hS (pointHom x)).obj (A₂))))
      ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj (A₁)))
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₁)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₁)))
      ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj (A₂)))
      (@CategoryTheory.Functor.map _ _ ((BigFppfOver.toScheme B S hS).obj T').Modules
        Scheme.Modules.instCategory (zariskiReadingFunctor T')
        ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((modulePullback B S hS (pointHom x)).obj (A₂)))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))
        ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app (A₂)))
      ((zariskiReadingPullbackHom h).app ((modulePullback B S hS (pointHom x)).obj ((A₁ ⊗ A₂))))
      ((modulePullbackCompIso B S hS (representedSpaceMap B S hS h) (pointHom x)).hom.app
        ((A₁ ⊗ A₂)))
      (modulePullbackTensorIso B S hS ((representedSpaceMap B S hS h) ≫ pointHom x) A₁ A₂).hom
      ((zariskiReadingTensorObjIso T'
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁))
        ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₂))
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          ((representedSpaceMap B S hS h) ≫ pointHom x) (A₁) hA₁)
        (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          ((representedSpaceMap B S hS h) ≫ pointHom x) (A₂) hA₂)).hom ≫
        (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj (A₁)))
          ((zariskiReadingFunctor T').obj
            ((modulePullback B S hS ((representedSpaceMap B S hS h) ≫ pointHom x)).obj
              (A₂)))).hom) :=
  CategoryTheory.Functor.tensorPasteConclusion_of_squares _ _ _ _
    (hc _ _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₁) hA₁)
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS (pointHom x) (A₂) hA₂))
    (zariskiReadingPullbackHom_tensorPasteNaturality X x h A₁ A₂)
    (modulePullbackCompIso_tensorPasteMiddle_point X x h A₁ A₂)
    (zariskiReadingTensorObjIso_bifunctorNaturalitySquare_point X x h A₁ A₂ hA₁ hA₂)

end Tensor

end AlgebraicGeometry.Space

end
