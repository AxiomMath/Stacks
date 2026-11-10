module

public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFirstPageRestriction
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFiltrationWedgeRespects
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsTensorWedge

/-!
# Wedging with a local form, on the restricted first page of 0FMN

Let `f : X ⟶ Y` be quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, `U ⊆ Y` open and
`ω` a local `p`-form on `U`. The Katz–Oda description of the first differential in
[Stacks, Tag 0FMN] compares the action of `ρ(f⁻¹ω)` on the graded pieces of `Ω^•_{X/S}` over
`V = f⁻¹U` with wedging by `ω` on the first page `Ω^• ⊗ ℋ^q_dR(X/Y)`. This file treats the
`Y`-side of that comparison.

## Main definitions

* `Stacks.DeRhamSmooth.restrictedFormsWedge`: `ω ∧ - : Ω^k|_U ⟶ Ω^{k'}|_U`, left multiplication by
  `ω`.
* `Stacks.DeRhamSmooth.restrictedFormsTensorWedge`: the wedge pairing `y ↦ ω ∧ y` on
  `(Ω^k ⊗ ℋ^q)|_U`.
* `Stacks.DeRhamSmooth.WedgeStepSquare`: the compatibility of the action of `ρ(f⁻¹ω)` with the
  identification of Section 0FMK at a cut.

## Main results

* `Stacks.DeRhamSmooth.localTensorMap_app_tmul`: `localTensorMap` of a local morphism `α` is
  `α ⊗ 1` on local pure tensors.
* `Stacks.DeRhamSmooth.localTensorMap_restrictedFormsWedge`: `localTensorMap` of `ω ∧ -` is
  `restrictedFormsTensorWedge`.
* `Stacks.DeRhamSmooth.restrictedHigherDirectImageAction_wedgeActionGr`: granted
  `WedgeStepSquare`, the action of `ρ(f⁻¹ω)` on the restricted first page is `(ω ∧ -) ⊗ 1`, at
  any names of the two cuts.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf
attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

section Wedge

variable (U : Opens Y.toRingedSpace)

/-- **Wedging with a local form `ω` of degree `p` over `U`**, as a morphism of `𝒪_U`-modules
`Ω^k_{Y/S}|_U ⟶ Ω^{k'}_{Y/S}|_U`, `p + k = k'`: left multiplication by `ω` in the algebra of
relative differential forms (`Stacks.Cohomology.HigherDirectImage.restrictedLeftMul`), read in
the degree `k'`. -/
def restrictedFormsWedge {p : ℤ}
    (ω : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.obj (op U))
    (k k' : ℤ) (h : p + k = k') :
    (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g k) ⟶
      (moduleRestriction Y.toRingedSpace U).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g k') :=
  restrictedLeftMul U
      ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).mul p k) ω ≫
    (moduleRestriction Y.toRingedSpace U).map
      (eqToHom (congrArg (AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).piece h))

end Wedge

section Local

variable (U : Opens Y.toRingedSpace)

/-- The tensor product of sheaves of modules acts on a pure tensor through its first factor. -/
private theorem sheafTensor_map_app_tensorSheafUnit {A A' : Modules Y.toRingedSpace} (θ : A ⟶ A')
    (B : Modules Y.toRingedSpace) (W : (Opens Y.toRingedSpace)ᵒᵖ) (a : A.val.obj W)
    (b : B.val.obj W) (c : A'.val.obj W) (hc : θ.val.app W a = c) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor Y.sheaf).map θ).app B).val.app W
        (Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace A B W a b) =
      Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace A' B W c b := by
  subst hc
  exact (PresheafOfModules.unit_naturality_apply
    (R := Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)
    (α := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf).obj)
    (PresheafOfModules.tensorHom θ.val (𝟙 B.val)) W (a ⊗ₜ b)).trans
    (congrArg (fun t ↦ (PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) A' B).app W t)
      (PresheafOfModules.tensorHom_tmul θ.val (𝟙 B.val) W a b))

/-- **`localTensorMap` on local pure tensors**: on the class of `η ⊗ s` over an open `W ⊆ U` it is
the class of `α(η) ⊗ s`. -/
theorem localTensorMap_app_tmul (q : ℤ) {M M' : Modules Y.toRingedSpace}
    (α : (moduleRestriction Y.toRingedSpace U).obj M ⟶ (moduleRestriction Y.toRingedSpace U).obj M')
    (W : (Opens (restrictToOpen Y.toRingedSpace U))ᵒᵖ)
    (η : ((moduleRestriction Y.toRingedSpace U).obj M).val.obj W)
    (s : ((moduleRestriction Y.toRingedSpace U).obj (deRhamCohomologySheaf f q)).val.obj W) :
    (localTensorMap f g U q α).val.app W
        (Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace M (deRhamCohomologySheaf f q)
          (op (U.isOpenEmbedding.functor.obj W.unop)) η s) =
      Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace M' (deRhamCohomologySheaf f q)
        (op (U.isOpenEmbedding.functor.obj W.unop)) (α.val.app W η) s := by
  have := isIso_moduleRestriction_coefficientFirstPageFlat_map_counit f g U q M
  have tri : ((restrictAdjunction U).counit.app M).val.app
      (op (U.isOpenEmbedding.functor.obj W.unop))
      (((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M)).val.app
        W η) =
        η :=
    congrArg (fun φ ↦ φ.val.app W η) ((restrictAdjunction U).right_triangle_components M)
  have hα : (((restrictAdjunction U).homEquiv _ _).symm α).val.app
      (op (U.isOpenEmbedding.functor.obj W.unop))
      (((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M)).val.app
        W η) =
      α.val.app W η :=
    (congrArg (fun φ ↦ φ.val.app W (((restrictAdjunction U).unit.app
      ((moduleRestriction Y.toRingedSpace U).obj M)).val.app W η))
      (moduleRestriction_map_homEquiv_symm U α)).trans (congrArg (α.val.app W) tri)
  have h1 := sheafTensor_map_app_tensorSheafUnit ((restrictAdjunction U).counit.app M)
    (deRhamCohomologySheaf f q) (op (U.isOpenEmbedding.functor.obj W.unop))
    (((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M)).val.app W η)
      s η tri
  have h2 := sheafTensor_map_app_tensorSheafUnit (((restrictAdjunction U).homEquiv _ _).symm α)
    (deRhamCohomologySheaf f q) (op (U.isOpenEmbedding.functor.obj W.unop))
    (((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M)).val.app W η)
      s _ hα
  refine Eq.trans (congrArg (fun t ↦ (localTensorMap f g U q α).val.app W t) h1.symm) ?_
  refine Eq.trans ?_ h2
  exact congrArg (fun φ ↦ φ.val.app W
      (Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace _ (deRhamCohomologySheaf f q)
        (op (U.isOpenEmbedding.functor.obj W.unop))
        (((restrictAdjunction U).unit.app ((moduleRestriction Y.toRingedSpace U).obj M)).val.app
          W η) s))
    (IsIso.hom_inv_id_assoc ((moduleRestriction (inverseImageBase g) U).map
      ((coefficientFirstPageFlat f g q).map ((restrictAdjunction U).counit.app M)))
      ((moduleRestriction (inverseImageBase g) U).map
        ((coefficientFirstPageFlat f g q).map (((restrictAdjunction U).homEquiv _ _).symm α))))

/-- The wedge pairing is linear over `𝒪_Y` in the section of `Ω^k ⊗ ℱ`. -/
theorem formsTensorWedgeSection_smul_right (H : Y.Modules) (p k : ℤ) (V : (Y.Opens)ᵒᵖ)
    (r : (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj V)
    (ω : (AlgebraicGeometry.Scheme.Hom.formsOnRing g p).val.obj V)
    (x : (AlgebraicGeometry.Scheme.Hom.formsTensor g H k).val.obj V) :
    AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection g H p k V ω (r • x) =
      r • AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection g H p k V ω x := by
  unfold AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection
  have ht : Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace
      (AlgebraicGeometry.Scheme.Hom.formsOnRing g p)
      (AlgebraicGeometry.Scheme.Hom.formsTensor g H k)
      V ω (r • x) = r • Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace
      (AlgebraicGeometry.Scheme.Hom.formsOnRing g p)
      (AlgebraicGeometry.Scheme.Hom.formsTensor g H k)
      V ω x := by
    unfold Stacks.PullbackTensorCoherence.tmul
    rw [TensorProduct.tmul_smul]
    exact map_smul _ _ _
  rw [ht]
  exact map_smul _ _ _

/-- The wedge pairing `Ω^p ⊗ (Ω^k ⊗ ℋ^q) ⟶ Ω^{p+k} ⊗ ℋ^q` on local sections, read as a bilinear
map of sheaves of `g^{-1}𝒪_S`-modules. -/
def formsTensorWedgeBilinear (q : ℤ) (p k : ℤ) :
    Stacks.BilinearMap ((pushforward (toInverseImageBase g)).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p)).val
      ((coefficientFirstPageFlat f g q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g k)).val
      ((coefficientFirstPageFlat f g q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (p + k))).val where
  app V := AddMonoidHom.mk' (fun ω ↦ AddMonoidHom.mk'
      (fun y ↦ AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection g (deRhamCohomologySheaf f q)
        p k V ω y)
      (fun y y' ↦ AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection_add_right g
        (deRhamCohomologySheaf f q) p k V ω y y'))
    (fun ω ω' ↦ AddMonoidHom.ext fun y ↦
      AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection_add_left g (deRhamCohomologySheaf f q)
        p k V ω ω' y)
  map_smul_left V _ ω y :=
    AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection_smul_left g (deRhamCohomologySheaf f q)
      p k V _ ω y
  map_smul_right V _ ω y :=
    formsTensorWedgeSection_smul_right g (deRhamCohomologySheaf f q) p k V _ ω y
  naturality i ω y :=
    AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection_restrict g (deRhamCohomologySheaf f q)
      p k i ω y

/-- **Wedging a local form `ω` of degree `p` over `U` into `(Ω^k ⊗ ℋ^q)|_U`**: over `W ⊆ U` it is
`y ↦ ω|_W ∧ y`, `AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection`. -/
def restrictedFormsTensorWedge (q : ℤ) {p : ℤ}
    (ω : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.obj (op U)) (k : ℤ) :
    (moduleRestriction (inverseImageBase g) U).obj ((coefficientFirstPageFlat f g q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g k)) ⟶
      (moduleRestriction (inverseImageBase g) U).obj ((coefficientFirstPageFlat f g q).obj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (p + k))) :=
  restrictedLeftMul (X := inverseImageBase g) U (formsTensorWedgeBilinear f g q p k) ω

section Ext

attribute [local instance] AlgebraicGeometry.SheafOfModules.hasSheafifyOpens
  AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijectiveOpens

/-- **`ω ∧ - ⊗ 1` is the wedge pairing with `ω`**: `localTensorMap` of wedging with a local form
`ω` is `y ↦ ω ∧ y` on every local section of `(Ω^k ⊗ ℋ^q)|_U`, not only on the pure tensors. -/
theorem localTensorMap_restrictedFormsWedge (q : ℤ) {p : ℤ}
    (ω : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.obj (op U)) (k : ℤ) :
    localTensorMap f g U q (restrictedFormsWedge g U ω k (p + k) rfl) =
      restrictedFormsTensorWedge f g U q ω k := by
  refine sub_eq_zero.mp ?_
  refine @restricted_hom_eq_zero_of_isLocallySurjective (inverseImageBase g) U _ _ _ _
    (CategoryTheory.toSheafify (Opens.grothendieckTopology (inverseImageBase g))
      (PresheafOfModules.tensorObj
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g k).val
        (deRhamCohomologySheaf f q).val).presheaf)
    (Presheaf.isLocallySurjective_toSheafify'
      (Opens.grothendieckTopology (inverseImageBase g)) _) ?_
  intro W r
  induction r using TensorProduct.inductionOn with
  | add a b ha hb => exact (congrArg _ (map_add _ a b)).trans ((map_add _ _ _).trans
      ((congrArg₂ (· + ·) ha hb).trans (add_zero 0)))
  | tmul x y =>
    have h1 := localTensorMap_app_tmul f g U q (restrictedFormsWedge g U ω k (p + k) rfl) (op W) x y
    have h2 := AlgebraicGeometry.Scheme.Hom.formsTensorWedgeSection_tmul g
      (deRhamCohomologySheaf f q) p k (op (openOfRestrict U W))
      ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.map
        (homOfLE (openOfRestrict_le U W)).op ω) x y
    change (localTensorMap f g U q (restrictedFormsWedge g U ω k (p + k) rfl)).val.app (op W)
        (Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace _ (deRhamCohomologySheaf f q)
          (op (U.isOpenEmbedding.functor.obj W)) x y) -
      (restrictedFormsTensorWedge f g U q ω k).val.app (op W)
        (Stacks.PullbackTensorCoherence.tmul Y.toRingedSpace _ (deRhamCohomologySheaf f q)
          (op (U.isOpenEmbedding.functor.obj W)) x y) = 0
    exact Eq.trans (congrArg (fun t ↦ t - _) h1) (sub_eq_zero.mpr h2.symm)

end Ext

end Local

section Action

open CochainComplex.HomComplex

variable [QuasiCompact f] [QuasiSeparated f] [Smooth f] (U : Y.Opens)

/-- **The action of the pull back of a local form on the restricted graded pieces**: for
`ω ∈ Ω^p_{Y/S}(U)` and `k + p = k'`, the morphism of complexes
`gr^kΩ^•_{X/S}|_V ⟶ (gr^{k'}Ω^•_{X/S}|_V)[p]`, `V = f⁻¹U`, induced by left multiplication with
`ρ(f⁻¹ω)` (`CochainComplex.Filtered.actionGr`). -/
abbrev wedgeActionGr (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k k' : ℤ)
    (hk : k + p = k') :=
  CochainComplex.Filtered.actionGr (respectsFiltration_restrictedLeftMulCochain f g U p ω)
    (respectsFiltration_δ_restrictedLeftMulCochain f g U p ω) k k' hk

/-- **The step-square compatibility of the action of `ω` at the cut `k`**: through the
identification of Section 0FMK of the graded pieces at the cuts `k` and `k + p`, the action of
`ρ(f⁻¹ω)` on `gr^k|_V` is `(ω ∧ -) ⊗ 1`, tested on the global maps out of
`f^{-1}(j_!(Ω^k|_U))[-k] ⊗ Ω^•_{X/Y}` given by the counit and by the extension of `ω ∧ -`. -/
def WedgeStepSquare (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k : ℕ) :
    Prop :=
  ((moduleRestriction (inverseImageBase (f ≫ g))
    (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      ((coefficientTargetComplex f g k).map ((restrictAdjunction U).counit.app
          (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g (k : ℤ))) ≫
        (gradedPieceIsoGradedTargetComplexOfStepSquares f g k (stepSquares f g k).1
          (stepSquares f g k).2).inv) ≫
      wedgeActionGr f g U p ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring) =
    ((moduleRestriction (inverseImageBase (f ≫ g))
      (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
      ((coefficientTargetComplex f g k).map (((restrictAdjunction U).homEquiv _ _).symm
          (restrictedFormsWedge g U ω (k : ℤ) ((k + p : ℕ) : ℤ) (by push_cast; ring))) ≫
        coefficientTargetComplexShiftHom f g k p _ ≫
        (CategoryTheory.shiftFunctor _ (p : ℤ)).map
          (gradedPieceIsoGradedTargetComplexOfStepSquares f g (k + p) (stepSquares f g (k + p)).1
            (stepSquares f g (k + p)).2).inv) ≫
      (((moduleRestriction (inverseImageBase (f ≫ g))
        (preimageOpen (relativeBase f g) U)).mapHomologicalComplex
          (ComplexShape.up ℤ)).commShiftIso (p : ℤ)).hom.app _

variable (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q))

/-- **The action of `ρ(f⁻¹ω)` on the restricted first page is `(ω ∧ -) ⊗ 1`**, at any names
`k = k₀`, `k' = k₀ + p` of the two cuts, granted the step-square compatibility at `k₀`. -/
theorem restrictedHigherDirectImageAction_wedgeActionGr (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (q : ℤ) (k₀ : ℕ)
    (hμ : WedgeStepSquare f g U p ω k₀) (k k' : ℤ) (hk : (k₀ : ℤ) = k)
    (hk' : ((k₀ + p : ℕ) : ℤ) = k') (hkk : k + p = k') :
    (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIso f g hflat k q).inv ≫
      restrictedHigherDirectImageAction (relativeBase f g) U (wedgeActionGr f g U p ω k k' hkk)
        (k + q) (k' + q) (by omega) ≫
      (moduleRestriction (inverseImageBase g) U).map
        (higherDirectImageGradedPieceFlatIso f g hflat k' q).hom =
      localTensorMap f g U q (restrictedFormsWedge g U ω k k' (by omega)) := by
  subst hk hk'
  exact restrictedHigherDirectImageAction_flatIso f g hflat U k₀ p q _ _ hμ

end Action

end Stacks.DeRhamSmooth
