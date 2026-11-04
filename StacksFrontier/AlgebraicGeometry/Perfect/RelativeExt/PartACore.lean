module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.QCohDerived
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.RelativeExtTarget
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.ApproximationHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# The comparison maps of [Stacks, Tag 08IF] (A), from a perfect approximation

Let `f : X ⟶ S` be a morphism of schemes, `𝒢` a bounded complex of `𝒪_X`-modules flat over `S`,
`E` an object of `D(𝒪_X)`, `P` a perfect object of `D(𝒪_X)` and `p : P ⟶ E`. Suppose that the
projection-formula morphism for `P^∨ ⊗^L 𝒢` is invertible on `D_QCoh(𝒪_S)`. Put
`K = Rf_*(P^∨ ⊗^L 𝒢)`. This file constructs, for every quasi-coherent `𝒪_S`-module `ℱ` and every
`i`, an additive map

`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ) ⟶ H^i(S, K ⊗^L_{𝒪_S} ℱ)`,

with `H^i(S, -)` read as `Ext^i_{𝒪_S}(𝒪_S, -)`, and proves that it is functorial in `ℱ`,
compatible with the boundary maps of short exact sequences of quasi-coherent modules, and
bijective in every degree `i ≤ m` when `p` is an approximation of `E` from `b - m - 1` and `𝒢`
lives in degrees `≥ b`. It is the precomposition with `p` followed by the identification
`Hom(P, Φ N) ≃+ Hom(𝒪_S, K ⊗^L N)` of `perfectStageHomEquiv`, transported to shifted morphisms.

## Main definitions

* `Stacks.Cohomology.RelativeExt.relativeExtGroup`: `Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`.
* `Stacks.Cohomology.RelativeExt.baseTensorGroup`: `H^i(S, K ⊗^L_{𝒪_S} ℱ)`.
* `Stacks.Cohomology.RelativeExt.partAMap`: the map `α^i_ℱ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

variable {X S : Scheme.{u}}

/-- **`Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ)`**: the `i`-th `Ext` group in `D(𝒪_X)` out of `E` into the
complex `𝒢 ⊗_{𝒪_X} f^*ℱ` with terms `𝒢^n ⊗_{𝒪_X} f^*ℱ` and differentials `d ⊗ 1`. -/
abbrev relativeExtGroup (f : X ⟶ S) (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (E : DStd X) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ) :=
  DerivedCategory.Ext E
    (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)) i

/-- **`H^i(S, K ⊗^L_{𝒪_S} ℱ)`**, read as `Ext^i_{𝒪_S}(𝒪_S, K ⊗^L_{𝒪_S} ℱ)`. -/
abbrev baseTensorGroup (K : DStd S) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (i : ℤ) :=
  DerivedCategory.Ext (derivedUnit S.toRingedSpace.sheaf)
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj K).obj
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) 0).obj
        F)) i

variable (f : X ⟶ S) {G : CochainComplex (TModules X.toRingedSpace) ℤ}
  (hG : IsBoundedFlatOver f.toLRSHom.toShHom G)

/-- For an object `K` of `D(𝒪_Z)`, the functor `K ⊗^L -` is additive. -/
instance derivedTensorObj_additive (Z : RingedSpace.{u, u})
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
      K).Additive := by
  letI : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj
      K).CommShift ℤ := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Z.sheaf).commShift_right K
  haveI := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Z.sheaf).exact_right K
  infer_instance

/-- For an object `K` of `D(𝒪_Z)`, the functor `- ⊗^L K` is additive. -/
instance derivedTensorFlipObj_additive (Z : RingedSpace.{u, u})
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).flip.obj
      K).Additive := by
  letI : ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
      Z.sheaf).flip.obj K).CommShift ℤ :=
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Z.sheaf).commShift_left K
  haveI := (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    Z.sheaf).exact_left K
  infer_instance

/-- The functor `Φ = Lf^*(-) ⊗^L 𝒢` from `D(𝒪_S)` to `D(𝒪_X)` is additive. -/
instance pullbackTensorDerivedFunctor_additive :
    (pullbackTensorDerivedFunctor hG).Additive := by
  haveI : (derivedPullbackTensorFunctor f.toLRSHom.toShHom G).Additive := by
    haveI : (derivedPushforward f.toLRSHom.toShHom).Additive := by
      letI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
        f.toLRSHom.toShHom
      haveI := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
        f.toLRSHom.toShHom
      infer_instance
    haveI : (derivedPullback f.toLRSHom.toShHom).Additive :=
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction
        f.toLRSHom.toShHom).left_adjoint_additive
    exact @Functor.instAdditiveComp _ _ _ _ _ _ (derivedPullback f.toLRSHom.toShHom) this _ _ _
      _ (derivedTensorFlipObj_additive X.toRingedSpace _)
  exact Functor.additive_of_iso (derivedPullbackTensorIso hG)

variable (P : DStd X) (hP : (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf).IsPerfect P)
  (hPF : ∀ N, qcohDerived S N →
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      f.toLRSHom.toShHom (stageSource (G := G) P) N))

/-- The identification `Hom(P, Φ N) ≃+ Hom(𝒪_S, K ⊗^L N)` on `D_QCoh(𝒪_S)`. -/
def partATheta :
    ShiftedHom.NaturalHomIdentification (pullbackTensorDerivedFunctor hG)
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
        (stageK f.toLRSHom.toShHom (G := G) P)) P (derivedUnit S.toRingedSpace.sheaf)
      (qcohDerived S) :=
  @ShiftedHom.NaturalHomEquiv.toIdentification _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorDerivedFunctor_additive f hG)
    (derivedTensorObj_additive S.toRingedSpace (stageK f.toLRSHom.toShHom (G := G) P))
    (perfectStageHomEquiv f.toLRSHom.toShHom hG P hP (qcohDerived S) hPF)
    (qcohDerived_biprod S)

/-- For an object `K` of `D(𝒪_Z)`, the functor `K ⊗^L -` commutes with shifts. -/
instance derivedTensorObj_commShift (Z : RingedSpace.{u, u})
    (K : Stacks.DerivedTensor.RingedSite.DerivedModules Z.sheaf) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.sheaf).obj K).CommShift ℤ :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).commShift_right K

variable {E : DStd X} (p : P ⟶ E)

/-- Precomposition with `p : P ⟶ E` and the identification `𝒢 ⊗ f^*ℱ ≅ Φ(ℱ[0])`. -/
def partAPrecomp (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) :
    relativeExtGroup f G E F i →+ ShiftedHom P ((pullbackTensorDerivedFunctor hG).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)) i where
  toFun y := p ≫ y ≫ ((relativeExtTargetIso hG).inv.app F)⟦i⟧'
  map_zero' := by simp
  map_add' y z := by simp only [Preadditive.add_comp, Preadditive.comp_add]

include hG hP hPF in
/-- The identification `Hom(P, Φ N[i]) ≃+ Hom(𝒪_S, (K ⊗^L N)[i])` for `N` in `D_QCoh(𝒪_S)`. -/
def partATransport (N : DStd S) (hN : qcohDerived S N) (i : ℤ) :
    ShiftedHom P ((pullbackTensorDerivedFunctor hG).obj N) i ≃+
      ShiftedHom (derivedUnit S.toRingedSpace.sheaf)
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
          (stageK f.toLRSHom.toShHom (G := G) P)).obj N) i :=
  @ShiftedHom.transport _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorDerivedFunctor_commShift hG) (derivedTensorObj_commShift S.toRingedSpace _)
    _ _ _ (partATheta f hG P hP hPF) (qcohDerived_shift S) N hN i

include hG hP hPF in
/-- `partATransport` is natural in `N`: it intertwines postcomposition with `Φ g` and with
`K ⊗^L g` for a morphism `g : N ⟶ N'` in `D_QCoh(𝒪_S)`. -/
theorem partATransport_naturality {N N' : DStd S} (hN : qcohDerived S N)
    (hN' : qcohDerived S N') (g : N ⟶ N') (i : ℤ)
    (x : ShiftedHom P ((pullbackTensorDerivedFunctor hG).obj N) i) :
    partATransport f hG P hP hPF N' hN' i (x ≫ ((pullbackTensorDerivedFunctor hG).map g)⟦i⟧') =
      partATransport f hG P hP hPF N hN i x ≫
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
          (stageK f.toLRSHom.toShHom (G := G) P)).map g)⟦i⟧' :=
  @ShiftedHom.transport_naturality _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorDerivedFunctor_commShift hG) (derivedTensorObj_commShift S.toRingedSpace _)
    _ _ _ (partATheta f hG P hP hPF) (qcohDerived_shift S) N N' hN hN' g i x

include hG hP hPF in
/-- **The map `α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*ℱ) ⟶ H^i(S, K ⊗^L ℱ)`.** -/
def partAMap (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hF : F.IsQuasicoherent) :
    relativeExtGroup f G E F i →+ baseTensorGroup (stageK f.toLRSHom.toShHom (G := G) P) F i :=
  (partATransport f hG P hP hPF _ (qcohDerived_single S F hF) i).toAddMonoidHom.comp
    (partAPrecomp f hG P p i F)

include hG hP hPF in
/-- `α^i_ℱ(y)` is `partATransport` applied to the composite of `p`, `y` and the identification
`𝒢 ⊗ f^*ℱ ≅ Φ(ℱ[0])`. -/
theorem partAMap_apply (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
    (hF : F.IsQuasicoherent) (y : relativeExtGroup f G E F i) :
    partAMap f hG P hP hPF p i F hF y =
      partATransport f hG P hP hPF _ (qcohDerived_single S F hF) i
        (p ≫ y ≫ ((relativeExtTargetIso hG).inv.app F)⟦i⟧') :=
  rfl

include hG hP hPF in
/-- **`α^i_ℱ` is functorial in the quasi-coherent module `ℱ`.** -/
theorem partAMap_naturality (i : ℤ) {F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)}
    (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
    (y : relativeExtGroup f G E F i) :
    partAMap f hG P hP hPF p i F' hF'
        (y ≫ (DerivedCategory.Q.map ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v))⟦i⟧') =
      partAMap f hG P hP hPF p i F hF y ≫
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
          (stageK f.toLRSHom.toShHom (G := G) P)).map
            ((DerivedCategory.singleFunctor _ 0).map v))⟦i⟧' := by
  have h := (relativeExtTargetIso hG).inv.naturality v
  have key : p ≫ (y ≫ (DerivedCategory.Q.map
      ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v))⟦i⟧') ≫
        ((relativeExtTargetIso hG).inv.app F')⟦i⟧' =
      (p ≫ y ≫ ((relativeExtTargetIso hG).inv.app F)⟦i⟧') ≫
        ((pullbackTensorDerivedFunctor hG).map
          ((DerivedCategory.singleFunctor _ 0).map v))⟦i⟧' := by
    have e : (shiftFunctor (DStd X) i).map (DerivedCategory.Q.map
          ((relativeExtTargetFunctor f.toLRSHom.toShHom G).map v)) ≫
          (shiftFunctor (DStd X) i).map ((relativeExtTargetIso hG).inv.app F') =
        (shiftFunctor (DStd X) i).map ((relativeExtTargetIso hG).inv.app F) ≫
          (shiftFunctor (DStd X) i).map ((pullbackTensorDerivedFunctor hG).map
            ((DerivedCategory.singleFunctor _ 0).map v)) :=
      ((Functor.map_comp _ _ _).symm.trans (congrArg (shiftFunctor (DStd X) i).map h)).trans
        (Functor.map_comp _ _ _)
    simp only [Category.assoc]
    exact congrArg (fun t => p ≫ y ≫ t) e
  exact (congrArg (partATransport f hG P hP hPF _ (qcohDerived_single S F' hF') i) key).trans
    (partATransport_naturality f hG P hP hPF (qcohDerived_single S F hF)
      (qcohDerived_single S F' hF') _ i _)

include hG hP hPF in
/-- **`α^i_ℱ` is bijective for `i ≤ m`** when `p` is an approximation of `E` from `b - m - 1`
(isomorphisms on cohomology in degrees `> b - m - 1`, a surjection in degree `b - m - 1`) and
`𝒢 ⊗ f^*ℱ` lies in `D^{≥ b}`. -/
theorem partAMap_bijective (b m : ℤ)
    (hp : ∀ j : ℤ, b - m - 1 < j → IsIso ((DerivedCategory.homologyFunctor _ j).map p))
    (he : Epi ((DerivedCategory.homologyFunctor _ (b - m - 1)).map p))
    (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (hF : F.IsQuasicoherent)
    (hY : (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)).IsGE b)
    (i : ℤ) (hi : i ≤ m) :
    Function.Bijective (partAMap f hG P hP hPF p i F hF) := by
  have h1 := @DerivedCategory.bijective_precomp_of_approximatesFrom _ _ _ _ _ _ p (b - m - 1)
    hp he (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F)) b hY i
    (by omega)
  let e := (shiftFunctor (DStd X) i).mapIso ((relativeExtTargetIso hG).app F)
  have h2 : Function.Bijective (fun z : P ⟶ (DerivedCategory.Q.obj
      ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧ => z ≫ e.inv) :=
    Function.bijective_iff_has_inverse.2 ⟨fun w => w ≫ e.hom,
      fun z => (Category.assoc _ _ _).trans ((congrArg (z ≫ ·) e.inv_hom_id).trans
        (Category.comp_id z)),
      fun w => (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) e.hom_inv_id).trans
        (Category.comp_id w))⟩
  have h3 : Function.Bijective (fun y : E ⟶ (DerivedCategory.Q.obj
      ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj F))⟦i⟧ => p ≫ y ≫ e.inv) := by
    convert h2.comp h1 using 1
    exact funext fun y => (Category.assoc _ _ _).symm
  exact (partATransport f hG P hP hPF _ (qcohDerived_single S F hF) i).bijective.comp h3

/-- Conjugating a composite of shifted morphisms by isomorphisms. -/
theorem _root_.CategoryTheory.ShiftedHom.comp_conj {C : Type*} [Category C] [HasShift C ℤ]
    {V W Y₃ Y₁ Z₃ Z₁ : C} {n m : ℤ} (q : V ⟶ W) (x : ShiftedHom W Y₃ n)
    (δ : ShiftedHom Y₃ Y₁ (1 : ℤ))
    (δ' : ShiftedHom Z₃ Z₁ (1 : ℤ)) (e₃ : Z₃ ≅ Y₃) (e₁ : Z₁ ≅ Y₁)
    (hδ : δ' ≫ e₁.hom⟦(1 : ℤ)⟧' = e₃.hom ≫ δ) (h : 1 + n = m) :
    q ≫ x.comp δ h ≫ e₁.inv⟦m⟧' = ShiftedHom.comp (q ≫ x ≫ e₃.inv⟦n⟧') δ' h := by
  have hδ' : δ ≫ e₁.inv⟦(1 : ℤ)⟧' = e₃.inv ≫ δ' := by
    rw [← cancel_epi e₃.hom, Iso.hom_inv_id_assoc, ← reassoc_of% hδ, ← Functor.map_comp,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [ShiftedHom.comp, Category.assoc]
  rw [← (shiftFunctorAdd' C 1 n m h).inv.naturality e₁.inv, Functor.comp_map,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hδ', Functor.map_comp_assoc]

variable {f} in
/-- The connecting map `𝒢 ⊗ f^*ℱ₃ ⟶ (𝒢 ⊗ f^*ℱ₁)[1]` of a short exact sequence of
`𝒪_S`-modules, from the short exact sequence of complexes `0 ⟶ 𝒢 ⊗ f^*ℱ₁ ⟶ 𝒢 ⊗ f^*ℱ₂ ⟶
𝒢 ⊗ f^*ℱ₃ ⟶ 0` (exact because `𝒢` is flat over `S`). -/
def relativeExtBoundary {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) :
    ShiftedHom (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj A.X₃))
      (DerivedCategory.Q.obj ((relativeExtTargetFunctor f.toLRSHom.toShHom G).obj A.X₁)) (1 : ℤ) :=
  DerivedCategory.triangleOfSESδ (shortExact_relativeExtTarget _ G hG.isFlatOver hA)

variable {f} in
/-- `map_singleδ_relativeExtTargetIso` with `Φ` of the connecting morphism read as a shifted
morphism: `δ(ℱ₃ ⟶ ℱ₁[1]).map Φ` corresponds to the connecting morphism of
`0 ⟶ 𝒢 ⊗ f^*ℱ₁ ⟶ 𝒢 ⊗ f^*ℱ₂ ⟶ 𝒢 ⊗ f^*ℱ₃ ⟶ 0`. -/
theorem map_singleδ_relativeExtTargetIso_shiftedHom
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) :
    (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ hA.singleδ _
      (pullbackTensorDerivedFunctor_commShift hG)) ≫
        ((relativeExtTargetIso hG).app A.X₁).hom⟦(1 : ℤ)⟧' =
      ((relativeExtTargetIso hG).app A.X₃).hom ≫ relativeExtBoundary hG hA :=
  (Category.assoc _ _ _).trans (map_singleδ_relativeExtTargetIso hG hA)

include hG hP hPF in
/-- `partATransport` is compatible with composition with a shifted morphism `δ : N₃ ⟶ N₁[1]`,
carried by `Φ` on the source side and by `K ⊗^L -` on the target side. -/
theorem partATransport_comp_map {N₃ N₁ : DStd S} (h₃ : qcohDerived S N₃)
    (h₁ : qcohDerived S N₁) (δ : ShiftedHom N₃ N₁ (1 : ℤ)) (n m : ℤ) (h : 1 + n = m)
    (x : ShiftedHom P ((pullbackTensorDerivedFunctor hG).obj N₃) n) :
    partATransport f hG P hP hPF N₁ h₁ m
        (x.comp
          (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ δ _ (pullbackTensorDerivedFunctor_commShift hG))
          h) =
      (partATransport f hG P hP hPF N₃ h₃ n x).comp
        (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ δ _ (derivedTensorObj_commShift S.toRingedSpace _))
        h :=
  @ShiftedHom.transport_comp_map _ _ _ _ _ _ _ _ _ _ _ _ _
    (pullbackTensorDerivedFunctor_commShift hG) (derivedTensorObj_commShift S.toRingedSpace _)
    _ _ _ (partATheta f hG P hP hPF) (qcohDerived_shift S) N₃ N₁ h₃ h₁ δ n m h x

include hG hP hPF in
/-- **`α_ℱ` is compatible with the boundary maps** of a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of quasi-coherent `𝒪_S`-modules: the boundary
`Ext^n(E, 𝒢 ⊗ f^*ℱ₃) ⟶ Ext^{n+1}(E, 𝒢 ⊗ f^*ℱ₁)` corresponds to the boundary
`H^n(S, K ⊗^L ℱ₃) ⟶ H^{n+1}(S, K ⊗^L ℱ₁)` of the distinguished triangle `K ⊗^L (ℱ₁ → ℱ₂ → ℱ₃)`. -/
theorem partAMap_boundary
    {A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace))}
    (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent) (n m : ℤ)
    (h : 1 + n = m) (y : relativeExtGroup f G E A.X₃ n) :
    partAMap f hG P hP hPF p m A.X₁ h₁ (y.comp (relativeExtBoundary hG hA) h) =
      (partAMap f hG P hP hPF p n A.X₃ h₃ y).comp
        (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ hA.singleδ _
          (derivedTensorObj_commShift S.toRingedSpace _)) h := by
  have hδ2 := map_singleδ_relativeExtTargetIso_shiftedHom hG hA
  have key := ShiftedHom.comp_conj p y (relativeExtBoundary hG hA)
    (@ShiftedHom.map _ _ _ _ _ _ _ _ _ _ _ hA.singleδ _
      (pullbackTensorDerivedFunctor_commShift hG))
    ((relativeExtTargetIso hG).app A.X₃) ((relativeExtTargetIso hG).app A.X₁)
    hδ2 h
  exact (congrArg (partATransport f hG P hP hPF _ (qcohDerived_single S A.X₁ h₁) m) key).trans
    (partATransport_comp_map f hG P hP hPF (qcohDerived_single S A.X₃ h₃)
      (qcohDerived_single S A.X₁ h₁) hA.singleδ n m h _)

end Stacks.Cohomology.RelativeExt

end
