module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMateSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackTensorMateNaturality

/-!
# The base change of the Zariski reading is monoidal

For `h : T' ⟶ T`, the base change along `h` of the Zariski reading of quasi-coherent modules is
monoidal, first in the tensor product sheaf
(`AlgebraicGeometry.Space.zariskiReadingTensorSquare_sheafTensor`) and then in the monoidal
products, through the identifications `AlgebraicGeometry.Space.modulesTensorObjIso` of the
monoidal product with the tensor product sheaf on both sides, the naturality of the base change,
and Stacks 03EL for the morphism of represented spaces.

## Main results

* `AlgebraicGeometry.Space.zariskiReadingTensorSquare_sheafTensor`: the base change of the
  Zariski reading is monoidal in the tensor product sheaf.
* `CategoryTheory.Functor.tensorPasteUpper_of_comp`: the upper square of a bifunctor tensor
  paste from the same square for composites.
* `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquare`: the body of
  `AlgebraicGeometry.Space.ZariskiReadingPullbackTensorSquare`, for every `h`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u


namespace Stacks.SheafOfModules

universe w w' v u₁ v' u'

variable {X : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
    {Y : AlgebraicGeometry.RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- Stacks 03EL read through the identity of the pullback of modules is Stacks 03EL. -/
theorem pullbackTensorIsoTransport_refl_hom
    (M N : _root_.SheafOfModules.{w'} (Tensor.ringSheaf Y.O)) :
    (pullbackTensorIsoTransport f (Iso.refl _) M N).hom =
        ((pullbackTensorIso f).app (M, N)).hom := by
  have h1 : (Tensor.sheafTensor X.O).map (𝟙 (f.pullbackModules.obj M)) = 𝟙 _ :=
      CategoryTheory.Functor.map_id _ _
  have h2 : ((Tensor.sheafTensor X.O).obj (f.pullbackModules.obj M)).map
      (𝟙 (f.pullbackModules.obj N)) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  simp only [pullbackTensorIsoTransport, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.refl_inv,
    Iso.refl_hom, Functor.mapIso_hom, NatTrans.id_app, Category.id_comp, h1, h2]
  rfl

end Stacks.SheafOfModules

namespace CategoryTheory

/-- Cancelling the last factor `q⁻¹` of a composite of isomorphisms against `q`. -/
theorem Iso.trans_trans_symm_hom_comp_hom {C : Type*} [Category C] {A B D E : C} (a : A ≅ B)
    (p : B ≅ E) (q : D ≅ E) {c : B ⟶ E} (hc : p.hom = c) :
    (a ≪≫ p ≪≫ q.symm).hom ≫ q.hom = a.hom ≫ c := by
  subst hc; simp

end CategoryTheory

namespace AlgebraicGeometry.Space

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T T' : BigFppfOver B S hS} (h : T' ⟶ T)
variable (N M : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite)

/-- **The base change of the Zariski reading along `h` is monoidal on quasi-coherent modules**, in
the tensor product sheaf: the conclusion of
`AlgebraicGeometry.Space.zariskiReadingTensorSquareMateAux`. -/
theorem zariskiReadingTensorSquare_sheafTensor :
    ConclusionOf₂₀ (zariskiReadingTensorSquareMateAux h N M hN hM) :=
  zariskiReadingTensorSquareMateAux h N M hN hM (zariskiReadingTensorSquareMate_1 h N M hN hM)
      (zariskiReadingTensorSquareMate_2 h N M hN hM) (zariskiReadingTensorSquareMate_3 h N M hN hM)
      (zariskiReadingTensorSquareMate_4 h N M hN hM) (zariskiReadingTensorSquareMate_5 h N M hN hM)
      (zariskiReadingTensorSquareMate_6 h N M hN hM) (zariskiReadingTensorSquareMate_7 h N M hN hM)
      (zariskiReadingTensorSquareMate_8 h N M hN hM) (zariskiReadingTensorSquareMate_9 h N M hN hM)
      (zariskiReadingTensorSquareMate_10 h N M hN hM)
      (zariskiReadingTensorSquareMate_11 h N M hN hM)
      (zariskiReadingTensorSquareMate_12 h N M hN hM)
      (zariskiReadingTensorSquareMate_13 h N M hN hM)
      (zariskiReadingTensorSquareMate_14 h N M hN hM)
      (zariskiReadingTensorSquareMate_15 h N M hN hM)
      (zariskiReadingTensorSquareMate_16 h N M hN hM)
      (zariskiReadingTensorSquareMate_17 h N M hN hM)
      (zariskiReadingTensorSquareMate_18 h N M hN hM)
      (zariskiReadingTensorSquareMate_19 h N M hN hM)
      (zariskiReadingTensorSquareMate_20 h N M hN hM)

end AlgebraicGeometry.Space

namespace CategoryTheory

/-- The upper square of `CategoryTheory.Functor.bifunctor_tensor_paste_of_map` from the same
square for the composites `Z = R(m) ≫ Zs`, `Z' = R'(m') ≫ Zs'`, given the naturality of `θ'`
at `m` and the comparison `mφ ≫ m' = n ≫ cφ`. -/
theorem Functor.tensorPasteUpper_of_comp {𝒜 ℬ 𝒞 𝒟 : Type*} [Category 𝒜]
    [iℬ : Category ℬ] [i𝒞 : Category 𝒞] [Category 𝒟] {P : 𝒞 ⥤ ℬ} {R : 𝒟 ⥤ 𝒞} {R' : 𝒜 ⥤ ℬ}
    {F : ℬ ⥤ ℬ ⥤ ℬ} {D' Ds : 𝒟} {C' : 𝒞} {Y₁ Y₂ W₁ W₂ : ℬ} {GD' E' Gs Es : 𝒜}
    {Z : R.obj D' ⟶ C'} {κ : P.obj C' ⟶ (F.obj Y₁).obj Y₂} {a : Y₁ ⟶ W₁} {b : Y₂ ⟶ W₂}
    {θ' : P.obj (R.obj D') ⟶ R'.obj GD'} {mφ : GD' ⟶ E'} {Z' : R'.obj E' ⟶ (F.obj W₁).obj W₂}
    (m : D' ⟶ Ds) (Zs : R.obj Ds ⟶ C') (Ps : P.obj (R.obj Ds) ⟶ R'.obj Gs) (n : GD' ⟶ Gs)
    (cφ : Gs ⟶ Es) (m' : E' ⟶ Es) (Zs' : R'.obj Es ⟶ (F.obj W₁).obj W₂)
    (hZ : Z = R.map m ≫ Zs) (hZ' : Z' = R'.map m' ≫ Zs')
    (H : P.map Zs ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) = Ps ≫ R'.map cφ ≫ Zs')
    (hnat : P.map (R.map m) ≫ Ps = θ' ≫ R'.map n) (hmφ : mφ ≫ m' = n ≫ cφ) :
    Functor.TensorPasteUpper P R R' F Z κ a b θ' mφ Z' := by
  subst hZ hZ'
  show P.map (R.map m ≫ Zs) ≫ κ ≫ ((F.map a).app Y₂ ≫ (F.obj W₁).map b) =
    θ' ≫ R'.map mφ ≫ R'.map m' ≫ Zs'
  rw [Functor.map_comp, Category.assoc, H, ← Category.assoc, hnat, Category.assoc,
    ← R'.map_comp_assoc, ← hmφ, R'.map_comp_assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (ringedSpaceHom)

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor
attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {T T' : BigFppfOver B S hS}


/-- `AlgebraicGeometry.Space.monoidalTensorSheafTensorIso` is the identity. -/
theorem comp_monoidalTensorSheafTensorIso_hom (Y : Scheme.{u}) {X M N : Y.Modules} (f : X ⟶ M ⊗ N) :
    f ≫ (monoidalTensorSheafTensorIso Y M N).hom = f := Category.comp_id f

/-- `CategoryTheory.Functor.tensorPasteUpper_of_comp` at the base change of the Zariski reading
along `h`, with the Zariski reading tensor isomorphisms split into the identification of the
monoidal product with the tensor product sheaf and
`AlgebraicGeometry.Space.zariskiReadingTensorIso`. -/
def zariskiReadingPullbackTensorSquareUpperAux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 => (Functor.tensorPasteUpper_of_comp
      (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) N₀ M₀).hom
      (zariskiReadingTensorIso T N₀ M₀ hN₀ hM₀).hom
      ((zariskiReadingPullbackHom h₀).app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))).obj N₀).obj
          M₀))
      ((modulePullback B S hS (representedSpaceMap B S hS h₀)).map
          (modulesTensorObjIso B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) N₀ M₀).hom)
      (zariskiReadingSpaceTensorIso h₀ N₀ M₀).hom
      (modulesTensorObjIso B S hS (yoneda.obj T') (isAlgebraicSpace_yoneda B S hS T')
          ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj N₀)
          ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj M₀)).hom
      (zariskiReadingTensorIso T' ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj N₀)
          ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj M₀)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h₀) N₀ hN₀)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h₀) M₀ hM₀)).hom
      a1 a2 a3 a4 a5 :
    CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N₀) (M₀)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
              ((zariskiReadingFunctor T).obj (N₀))).obj ((zariskiReadingFunctor T).obj (M₀)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h₀)).obj
          ((zariskiReadingFunctor T).obj (N₀)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h₀)).obj
          ((zariskiReadingFunctor T).obj (M₀)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h₀)).obj (N₀)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h₀)).obj (M₀)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h₀)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N₀) (M₀))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
          (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS
          (representedSpaceMap B S hS h₀)).obj (N₀))
          ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj (M₀))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h₀)) (zariskiReadingFunctor T)
          (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N₀) (M₀) hN₀ hM₀).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N₀)) ((zariskiReadingFunctor T).obj (M₀))).hom)
          ((Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h₀).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N₀), (zariskiReadingFunctor T).obj (M₀)))
          ((zariskiReadingPullbackHom h₀).app (N₀)) ((zariskiReadingPullbackHom h₀).app (M₀))
          ((zariskiReadingPullbackHom h₀).app ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N₀)
          (M₀))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h₀) N₀ M₀).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj
          (N₀)) ((modulePullback B S hS (representedSpaceMap B S hS h₀)).obj (M₀))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h₀) (N₀) hN₀)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h₀) (M₀) hM₀)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h₀)).obj (N₀)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h₀)).obj (M₀)))).hom))

variable (h : T' ⟶ T) (N M : Modules.{u, u} B S hS (yoneda.obj T)
    (isAlgebraicSpace_yoneda B S hS T)) (hN : N.IsQuasicoherentOnSite)
    (hM : M.IsQuasicoherentOnSite)

/-- `CategoryTheory.comp_eq_comp_of_heq` at
`AlgebraicGeometry.Space.zariskiReadingTensorSquare_sheafTensor`: the third hypothesis of
`AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`. -/
def zariskiReadingPullbackTensorSquareUpper_3Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 => (comp_eq_comp_of_heq
      (zariskiReadingTensorSquare_sheafTensor h₀ N₀ M₀ hN₀ hM₀)
    a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 : HypothesisOf₅_3
        (zariskiReadingPullbackTensorSquareUpperAux h₀ N₀ M₀ hN₀ hM₀))

/-- The hypothesis of an implication, as a proposition. -/
abbrev HypothesisOf₁_1 {α1 β : Prop} (_ : α1 → β) : Prop := α1

/-- The fifth hypothesis of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`,
from `CategoryTheory.Iso.trans_trans_symm_hom_comp_hom`. -/
def zariskiReadingPullbackTensorSquareUpper_5Aux (h₀ : T' ⟶ T)
    (N₀ M₀ : Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T))
    (hN₀ : N₀.IsQuasicoherentOnSite) (hM₀ : M₀.IsQuasicoherentOnSite) :=
  fun hc => (Iso.trans_trans_symm_hom_comp_hom _ _ _ hc : HypothesisOf₅_5
      (zariskiReadingPullbackTensorSquareUpperAux h₀ N₀ M₀ hN₀ hM₀))

/-- The hypothesis of
`AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpper_5Aux`: Stacks 03EL for the
morphism of represented spaces, read through the identity. -/
theorem zariskiReadingPullbackTensorSquareUpper_5_1 : HypothesisOf₁_1
    (zariskiReadingPullbackTensorSquareUpper_5Aux h N M hN hM) :=
  (Stacks.SheafOfModules.pullbackTensorIsoTransport_refl_hom
      (smallEtaleRingedToposModulesHom B S hS (representedSpaceMap B S hS h)) N M).symm

/-- Hypothesis 1 of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`:
the Zariski reading tensor isomorphism at `T` is the Zariski reading of the identification of
the monoidal product with the tensor product sheaf, followed by
`AlgebraicGeometry.Space.zariskiReadingTensorIso`. -/
theorem zariskiReadingPullbackTensorSquareUpper_1 : HypothesisOf₅_1
    (zariskiReadingPullbackTensorSquareUpperAux h N M hN hM) :=
  comp_monoidalTensorSheafTensorIso_hom _ _
/-- Hypothesis 2 of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`:
the same at `T'`. -/
theorem zariskiReadingPullbackTensorSquareUpper_2 : HypothesisOf₅_2
    (zariskiReadingPullbackTensorSquareUpperAux h N M hN hM) :=
  comp_monoidalTensorSheafTensorIso_hom _ _
/-- Hypothesis 3 of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`:
the monoidality square in the tensor product sheaf. -/
theorem zariskiReadingPullbackTensorSquareUpper_3 : HypothesisOf₅_3
    (zariskiReadingPullbackTensorSquareUpperAux h N M hN hM) :=
  zariskiReadingPullbackTensorSquareUpper_3Aux h N M hN hM rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
      HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
/-- Hypothesis 4 of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`:
the naturality of the base change of the Zariski reading. -/
theorem zariskiReadingPullbackTensorSquareUpper_4 : HypothesisOf₅_4
    (zariskiReadingPullbackTensorSquareUpperAux h N M hN hM) :=
  (zariskiReadingPullbackHom h).naturality _
/-- Hypothesis 5 of `AlgebraicGeometry.Space.zariskiReadingPullbackTensorSquareUpperAux`:
Stacks 03EL for the morphism of represented spaces in the two spellings. -/
theorem zariskiReadingPullbackTensorSquareUpper_5 : HypothesisOf₅_5
    (zariskiReadingPullbackTensorSquareUpperAux h N M hN hM) :=
  zariskiReadingPullbackTensorSquareUpper_5Aux h N M hN hM
      (zariskiReadingPullbackTensorSquareUpper_5_1 h N M hN hM)

/-- **The base change of the Zariski reading is monoidal on quasi-coherent modules**: the body of
`AlgebraicGeometry.Space.ZariskiReadingPullbackTensorSquare` holds for every `h : T' ⟶ T`. -/
theorem zariskiReadingPullbackTensorSquare (h : T' ⟶ T) :
  ∀ (N M : Modules.{u, u} B S hS (yonedaSpace B S hS T).1 (yonedaSpace B S hS T).2)
    (hN : N.IsQuasicoherentOnSite) (hM : M.IsQuasicoherentOnSite),
    CategoryTheory.Functor.TensorPasteUpper
      (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (iℬ := Scheme.Modules.instCategory)
      (𝒞 := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (i𝒞 := Scheme.Modules.instCategory)
      (D' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M)))
      (C' := (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T).presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T).presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T).ringCatSheaf.2⟩)).obj
              ((zariskiReadingFunctor T).obj (N))).obj ((zariskiReadingFunctor T).obj (M)))
      (Y₁ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (N)))
      (Y₂ := (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).obj
          ((zariskiReadingFunctor T).obj (M)))
      (W₁ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)))
      (W₂ := (zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))
      (GD' := (modulePullback B S hS (representedSpaceMap B S hS h)).obj
          ((MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T)
          (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (E' := (MonoidalCategory.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj T')
          (isAlgebraicSpace_yoneda B S hS T')) ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N))
          ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))))
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T)
          (zariskiReadingFunctor T') (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((BigFppfOver.toScheme B S hS).obj T').presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ ((BigFppfOver.toScheme B S hS).obj T').presheaf
          (forget₂ CommRingCat RingCat) ((BigFppfOver.toScheme B S hS).obj T').ringCatSheaf.2⟩)
      ((zariskiReadingTensorObjIso T (N) (M) hN hM).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T)
          ((zariskiReadingFunctor T).obj (N)) ((zariskiReadingFunctor T).obj (M))).hom)
          ((Stacks.RingedSpace.comparisonBifunctorIso
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom).hom.app
          ((zariskiReadingFunctor T).obj (N), (zariskiReadingFunctor T).obj (M)))
          ((zariskiReadingPullbackHom h).app (N)) ((zariskiReadingPullbackHom h).app (M))
          ((zariskiReadingPullbackHom h).app ((MonoidalCategory.tensorObj
          (C := Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)) (N) (M))))
      (modulePullbackTensorIso B S hS (representedSpaceMap B S hS h) N M).hom
      ((zariskiReadingTensorObjIso T' ((modulePullback B S hS (representedSpaceMap B S hS h)).obj
          (N)) ((modulePullback B S hS (representedSpaceMap B S hS h)).obj (M))
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (N) hN)
          (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
          (representedSpaceMap B S hS h) (M) hM)).hom ≫
          (monoidalTensorSheafTensorIso ((BigFppfOver.toScheme B S hS).obj T')
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (N)))
          ((zariskiReadingFunctor T').obj ((modulePullback B S hS
          (representedSpaceMap B S hS h)).obj (M)))).hom) := fun N M hN hM =>
  zariskiReadingPullbackTensorSquareUpperAux h N M hN hM
      (zariskiReadingPullbackTensorSquareUpper_1 h N M hN hM)
      (zariskiReadingPullbackTensorSquareUpper_2 h N M hN hM)
    (zariskiReadingPullbackTensorSquareUpper_3 h N M hN hM)
        (zariskiReadingPullbackTensorSquareUpper_4 h N M hN hM)
        (zariskiReadingPullbackTensorSquareUpper_5 h N M hN hM)

end AlgebraicGeometry.Space
