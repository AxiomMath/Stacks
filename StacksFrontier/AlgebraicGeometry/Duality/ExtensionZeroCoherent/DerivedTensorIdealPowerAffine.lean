module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangleExtensionCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerMap
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DerivedTensorIdealPowerResolution
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProSeqIsoOfProInverse
public import StacksFrontier.AlgebraicGeometry.Modules.TildeKFlat
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent.Affine
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeReflect
public import StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor
import all StacksFrontier.RingTheory.Module.AdicSystem.IdealPowerTensor

/-!
# The pro-isomorphism `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` on an affine Noetherian scheme

Let `R` be a Noetherian ring, `𝓘` a quasi-coherent sheaf of ideals on `Spec R` with ideal of global
sections `I`, and `𝓕^•` a bounded complex of coherent `𝒪_{Spec R}`-modules. This file proves that
the canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` of `AlgebraicGeometry.derivedTensorIdealPowerNatTrans`
have pro-inverses in `D(𝒪_{Spec R})`. This is the affine case of [Stacks, Tag 0G4U], and it is
[Stacks, Tag 0G3N] transported along `M ↦ M̃`.

The proof follows the Stacks Project. Write `𝓕^• = M̃^•` for the complex `M^•` of global sections,
a bounded complex of finite `R`-modules, and choose a bounded-above resolution `P^• ⟶ M^•` by
finite free modules for which the adic reductions are pro-isomorphic
(`Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction`). The
canonical maps are natural in the complex, so it suffices to treat `P̃^•` and the maps
`𝓘^n P̃^• ⟶ 𝓘^n 𝓕^•`:

* `P̃^•` is K-flat (Stacks 08DV) and its terms have flat global sections, so on `P̃^•` the
  canonical maps are isomorphisms: the multiplication `𝓖 ⊗ 𝓘^n ⟶ 𝓘^n 𝓖` is an isomorphism for
  quasi-coherent `𝓖` with flat global sections, which is checked on global sections using the
  tensor half of Stacks 01I8;
* the associated sheaf of `I^{n+1} N^•` is `𝓘^{n+1} Ñ^•`, naturally in `N^•`, so derived
  sheafification carries the algebraic pro-isomorphism `I^{n+1} P^• ⟶ I^{n+1} M^•` to the maps
  `𝓘^{n+1} P̃^• ⟶ 𝓘^{n+1} M̃^•`, and the shift `n ↦ n + 1` does not affect pro-inverses.

## Main results

* `AlgebraicGeometry.derivedTensorIdealPowerNatTrans_naturality`: the canonical maps are natural
  in the complex.
* `AlgebraicGeometry.isIso_idealPowerTensorMul_of_flat`: on `Spec R`, the multiplication map
  `𝓖 ⊗ 𝓘^n ⟶ 𝓘^n 𝓖` is an isomorphism for `𝓖` quasi-coherent with flat global sections.
* `AlgebraicGeometry.proInverse_derivedTensorIdealPowerNatTrans_spec`: the affine case of
  [Stacks, Tag 0G4U].

## Implementation notes

The ideal-power complexes `I^{n+1} N^•` of the algebraic statement are images of multiplication
maps of complexes and are indexed with the exponent shifted by one; they are compared with the
subsheaves `𝓘^{n+1} Ñ^i` through their global sections, using that a morphism of quasi-coherent
modules on an affine scheme is an isomorphism once it is one on global sections.

## References

* [Stacks Project, Tag 0G4U](https://stacks.math.columbia.edu/tag/0G4U)
* [Stacks Project, Tag 0G3N](https://stacks.math.columbia.edu/tag/0G3N)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 20000] _root_.Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

universe u

namespace AlgebraicGeometry

/-- Pasting a naturality square with the image of a commuting square under a functor. -/
private lemma comp_comp_eq_of_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B Z Z' : C} {X Y : D} {i : A ⟶ Z} {g : Z ⟶ Z'} {w : A ⟶ B} {j : B ⟶ Z'}
    (hc : i ≫ g = w ≫ j) {u : X ⟶ Y} {fA : X ⟶ F.obj A} {fB : Y ⟶ F.obj B}
    (hnat : u ≫ fB = fA ≫ F.map w) : u ≫ fB ≫ F.map j = (fA ≫ F.map i) ≫ F.map g := by
  rw [← Category.assoc, hnat, Category.assoc, ← F.map_comp, ← hc, F.map_comp, Category.assoc]

/-! ### Pro-inverses of maps of inverse sequences -/

section ProInverse

variable {C D : Type*} [Category C] [Category D]

/-- A map of inverse sequences has pro-inverses: each level acquires a two-sided inverse after
passing to a later level. -/
private abbrev HasProInv {A B : ℕᵒᵖ ⥤ C} (φ : A ⟶ B) : Prop :=
  ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : B.obj (op m) ⟶ A.obj (op n)),
    φ.app (op m) ≫ s = A.map (homOfLE h).op ∧ s ≫ φ.app (op n) = B.map (homOfLE h).op

/-- Pro-inverses are carried along by a functor: this is
`Stacks.AdicSystem.DerivedReductionProIso.HasProInverse.whiskerRight`, read for sequences. -/
private lemma hasProInv_whiskerRight {A B : ℕᵒᵖ ⥤ C} {φ : A ⟶ B} (hφ : HasProInv φ)
    (G : C ⥤ D) : HasProInv (Functor.whiskerRight φ G) := by
  have hφ' : Stacks.AdicSystem.DerivedReductionProIso.HasProInverse φ := fun j => by
    obtain ⟨m, h, s, hs, hs'⟩ := hφ j.unop
    exact ⟨op m, (homOfLE h).op, s, hs, hs'⟩
  intro n
  obtain ⟨k, f, s, hs, hs'⟩ := hφ'.whiskerRight G (op n)
  exact ⟨k.unop, leOfHom f.unop, s, hs, hs'⟩

/-- Pro-inverses of a map of inverse sequences follow from pro-inverses of its restriction to
the positive indices. -/
private lemma hasProInv_of_whiskerLeft_successor {A B : ℕᵒᵖ ⥤ C} {φ : A ⟶ B}
    (hφ : HasProInv (Functor.whiskerLeft
      Stacks.AdicSystem.DerivedReductionProIso.successorOp φ)) : HasProInv φ := by
  intro n
  obtain ⟨m, h, s₀, hs, hs'⟩ := hφ n
  let s : B.obj (op (m + 1)) ⟶ A.obj (op (n + 1)) := s₀
  replace hs : φ.app (op (m + 1)) ≫ s = A.map (homOfLE (Nat.add_le_add_right h 1)).op := hs
  replace hs' : s ≫ φ.app (op (n + 1)) = B.map (homOfLE (Nat.add_le_add_right h 1)).op := hs'
  have h' : n ≤ m + 1 := h.trans (Nat.le_succ m)
  let t : A.obj (op (n + 1)) ⟶ A.obj (op n) := A.map (homOfLE (Nat.le_succ n)).op
  refine ⟨m + 1, h', s ≫ t, ?_, ?_⟩
  · calc φ.app (op (m + 1)) ≫ s ≫ t = (φ.app (op (m + 1)) ≫ s) ≫ t :=
          (Category.assoc _ _ _).symm
      _ = A.map (homOfLE (Nat.add_le_add_right h 1)).op ≫ t := congrArg (· ≫ t) hs
      _ = A.map (homOfLE h').op := (A.map_comp _ _).symm
  · calc (s ≫ t) ≫ φ.app (op n) = s ≫ (t ≫ φ.app (op n)) := Category.assoc _ _ _
      _ = s ≫ (φ.app (op (n + 1)) ≫ B.map (homOfLE (Nat.le_succ n)).op) :=
          congrArg (s ≫ ·) (φ.naturality _)
      _ = (s ≫ φ.app (op (n + 1))) ≫ B.map (homOfLE (Nat.le_succ n)).op :=
          (Category.assoc _ _ _).symm
      _ = B.map (homOfLE (Nat.add_le_add_right h 1)).op ≫
            B.map (homOfLE (Nat.le_succ n)).op := congrArg (· ≫ _) hs'
      _ = B.map (homOfLE h').op := (B.map_comp _ _).symm

end ProInverse

/-! ### Naturality of the canonical maps in the complex -/

section Naturality

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- **The map of inverse systems `(K ⊗^L 𝓘^n)_n ⟶ (L ⊗^L 𝓘^n)_n`** induced by a morphism
`K ⟶ L` of `D(𝒪_X)`. -/
public def derivedTensorIdealPowerSystemMap {K L : DerivedCategory X.Modules} (g : K ⟶ L) :
    derivedTensorIdealPowerSystem I K ⟶ derivedTensorIdealPowerSystem I L :=
  NatTrans.ofOpSequence
    (fun n => ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.map g).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n)))
    (fun n => by
      let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
      let tr := (DerivedCategory.singleFunctor X.Modules 0).map (idealPowerSheafTransition I n)
      have hK : (derivedTensorIdealPowerSystem I K).map (homOfLE (Nat.le_succ n)).op =
          (T.tensor.obj K).map tr := Functor.ofOpSequence_map_homOfLE_succ _ n
      have hL : (derivedTensorIdealPowerSystem I L).map (homOfLE (Nat.le_succ n)).op =
          (T.tensor.obj L).map tr := Functor.ofOpSequence_map_homOfLE_succ _ n
      rw [hK, hL]
      exact (T.tensor.map g).naturality tr)

/-- The components of `AlgebraicGeometry.derivedTensorIdealPowerSystemMap`. -/
public lemma derivedTensorIdealPowerSystemMap_app {K L : DerivedCategory X.Modules} (g : K ⟶ L) :
    (derivedTensorIdealPowerSystemMap I g).app (op n) =
      ((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.map g).app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (idealPowerSheaf I n)) :=
  rfl

/-- The map of inverse systems induced by an isomorphism is levelwise an isomorphism. -/
public lemma isIso_derivedTensorIdealPowerSystemMap_app {K L : DerivedCategory X.Modules}
    (g : K ≅ L) : IsIso ((derivedTensorIdealPowerSystemMap I g.hom).app (op n)) := by
  rw [derivedTensorIdealPowerSystemMap_app]
  exact Iso.isIso_hom
    (((Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace).tensor.mapIso g).app _)

/-- `m ⊗ a ↦ a • m`, factored through `𝓘^n 𝓜`, is natural in the module. -/
public lemma idealPowerTensorMul_naturality {M M' : X.Modules} (f : M ⟶ M') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map f).app (idealPowerSheaf I n) ≫
        idealPowerTensorMul I n M' =
      idealPowerTensorMul I n M ≫ DeligneTriangle.idealPowerTermMap I n f := by
  apply cancel_sheafSubmodule_ι (idealPowerMultiple I n M')
  refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (idealPowerTensorMul_ι I n M'))).trans ?_
  refine (idealPowerTensorMulAmbient_naturality I n f).trans ?_
  refine (congrArg (· ≫ f) (idealPowerTensorMul_ι I n M).symm).trans ?_
  refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
  exact congrArg (_ ≫ ·) (DeligneTriangle.idealPowerTermMap_comp_ι I n f).symm

/-- The termwise multiplication maps are natural in the complex. -/
public lemma idealPowerRowMap_naturality {G F : CochainComplex X.Modules ℤ} (f : G ⟶ F) :
    CochainComplex.KFlatBifunctor.rowComplexMap (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (show (show Stacks.Duality.TensorComplex X from G) ⟶
          (show Stacks.Duality.TensorComplex X from F) from f) (idealPowerSheaf I n) ≫
        idealPowerRowMap I n F =
      idealPowerRowMap I n G ≫ DeligneTriangle.idealPowerComplexMap I f n := by
  ext p : 1
  exact idealPowerTensorMul_naturality I n (f.f p)

/-- The multiplication maps of complexes `Tot(𝓕^• ⊗ 𝓘^n[0]) ⟶ 𝓘^n 𝓕^•` are natural in the
complex. -/
public lemma idealPowerTensorComplexMap_naturality {G F : CochainComplex X.Modules ℤ}
    (f : G ⟶ F) :
    HomologicalComplex.mapBifunctorMap
        (show (show Stacks.Duality.TensorComplex X from G) ⟶
          (show Stacks.Duality.TensorComplex X from F) from f)
        (𝟙 (idealPowerSingle I n)) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ) ≫ idealPowerTensorComplexMap I n F =
      idealPowerTensorComplexMap I n G ≫ DeligneTriangle.idealPowerComplexMap I f n := by
  let f' : (show Stacks.Duality.TensorComplex X from G) ⟶
      (show Stacks.Duality.TensorComplex X from F) := f
  have h1 := CochainComplex.KFlatBifunctor.totalSingleIso_hom_naturality
    (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) f' (idealPowerSheaf I n)
  have h2 := idealPowerRowMap_naturality I n f
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ idealPowerRowMap I n F) h1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.assoc _ _ _).symm)))

/-- **The canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` are natural in the complex `𝓕^•`.** -/
public lemma derivedTensorIdealPowerMap_naturality_left {G F : CochainComplex X.Modules ℤ}
    (f : G ⟶ F) :
    (derivedTensorIdealPowerSystemMap I (DerivedCategory.Q.map f)).app (op n) ≫
        derivedTensorIdealPowerMap I n F =
      derivedTensorIdealPowerMap I n G ≫
        DerivedCategory.Q.map (DeligneTriangle.idealPowerComplexMap I f n) := by
  let T := Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace
  let G' : Stacks.Duality.TensorComplex X := G
  let F' : Stacks.Duality.TensorComplex X := F
  let f' : G' ⟶ F' := f
  let s := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app (idealPowerSheaf I n)
  let α := T.tensor.map (DerivedCategory.Q.map f')
  have hnat := α.naturality s
  have htt : α.app (DerivedCategory.Q.obj (idealPowerSingle I n)) ≫
      T.toTensor F' (idealPowerSingle I n) =
      T.toTensor G' (idealPowerSingle I n) ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap f' (𝟙 (idealPowerSingle I n))
          (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)) := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using
      T.toTensor_naturality f' (𝟙 (idealPowerSingle I n))
  have hc : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap f'
        (𝟙 (idealPowerSingle I n)) (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)
        (ComplexShape.up ℤ)) ≫ DerivedCategory.Q.map (idealPowerTensorComplexMap I n F) =
      DerivedCategory.Q.map (idealPowerTensorComplexMap I n G) ≫
        DerivedCategory.Q.map (DeligneTriangle.idealPowerComplexMap I f n) :=
    (DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (idealPowerTensorComplexMap_naturality I n f)).trans
        (DerivedCategory.Q.map_comp _ _))
  let τF := T.toTensor F' (idealPowerSingle I n)
  let τG := T.toTensor G' (idealPowerSingle I n)
  let cF := DerivedCategory.Q.map (idealPowerTensorComplexMap I n F)
  let cG := DerivedCategory.Q.map (idealPowerTensorComplexMap I n G)
  let GF := T.tensor.obj (DerivedCategory.Q.obj F')
  let GG := T.tensor.obj (DerivedCategory.Q.obj G')
  change α.app _ ≫ GF.map s ≫ τF ≫ cF = (GG.map s ≫ τG ≫ cG) ≫ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τF ≫ cF) hnat.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (GG.map s ≫ ·)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cF) htt).trans
        ((Category.assoc _ _ _).trans ((congrArg (τG ≫ ·) hc).trans
          (Category.assoc _ _ _).symm))))).trans
      (Category.assoc _ _ _).symm)))

/-- **The comparison `(𝓕^• ⊗^L 𝓘^n)_n ⟶ (𝓘^n 𝓕^•)_n` is natural in the complex `𝓕^•`.** -/
public lemma derivedTensorIdealPowerNatTrans_naturality {G F : CochainComplex X.Modules ℤ}
    (f : G ⟶ F) :
    derivedTensorIdealPowerSystemMap I (DerivedCategory.Q.map f) ≫
        derivedTensorIdealPowerNatTrans I F =
      derivedTensorIdealPowerNatTrans I G ≫
        Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans I f)
          DerivedCategory.Q := by
  ext ⟨n⟩
  refine ((NatTrans.comp_app _ _ _).trans ?_).trans (NatTrans.comp_app _ _ _).symm
  rw [derivedTensorIdealPowerNatTrans_app, derivedTensorIdealPowerNatTrans_app]
  exact derivedTensorIdealPowerMap_naturality_left I n f

end Naturality


/-! ### The canonical maps on a K-flat complex -/

section Resolution

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **On a K-flat complex whose multiplication maps are isomorphisms, the canonical map
`𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` is an isomorphism**: it is computed on the identity resolution
(`AlgebraicGeometry.derivedTensorIdealPowerMap_eq_resolutionIsoApp`). -/
public lemma isIso_derivedTensorIdealPowerMap_of_kFlat (F : CochainComplex X.Modules ℤ)
    (hF : Stacks.Duality.KFlatComplex (show Stacks.Duality.TensorComplex X from F)) (n : ℕ)
    (h : IsIso (idealPowerTensorComplexMap I n F)) :
    IsIso (derivedTensorIdealPowerMap I n F) := by
  let F' : Stacks.Duality.TensorComplex X := F
  have hid : HomologicalComplex.mapBifunctorMap (𝟙 F') (𝟙 (idealPowerSingle I n))
      (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ) = 𝟙 _ := by
    change ((Stacks.SheafOfModules.Tensor.tensorComplex X.sheaf).map (𝟙 F')).app _ = _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have e : idealPowerResolutionMap I n (𝟙 F') = idealPowerTensorComplexMap I n F :=
    (congrArg (· ≫ idealPowerTensorComplexMap I n F) hid).trans (Category.id_comp _)
  rw [derivedTensorIdealPowerMap_eq_resolutionIsoApp I hF (𝟙 F') n, e]
  have h₂ : IsIso (DerivedCategory.Q.map (idealPowerTensorComplexMap I n F)) :=
    Functor.map_isIso (F := DerivedCategory.Q) (f := idealPowerTensorComplexMap I n F)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h₂

end Resolution

/-! ### The multiplication map `𝓜 ⊗ 𝓘^n ⟶ 𝓘^n 𝓜` on affine sections -/

section AffineSections

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)

/-- Over an affine open, every section of `𝓘^n 𝓜 ⊆ 𝓜` is the image of a section of `𝓜 ⊗ 𝓘^n`
under multiplication, for `𝓜` quasi-coherent: the sections of `𝓘^n 𝓜` there are `𝓘(W)^n 𝓜(W)`,
whose elements are finite sums of products `a • m`, the images of the pure tensors `m ⊗ a`. -/
public lemma exists_idealPowerTensorMulAmbient_app_eq (M : X.Modules) [M.IsQuasicoherent]
    (W : X.affineOpens) (v : Γ(M, W.1))
    (hv : v ∈ (idealPowerMultiple I n M).toSubmodule.obj (op W.1)) :
    ∃ s, ((idealPowerTensorMulAmbient I n M).val.app (op W.1)).hom s = v := by
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple I n M W] at hv
  refine Submodule.smul_induction_on hv (fun r hr m _ => ?_) ?_
  · have hr' : r ∈ (idealPowerMultiple I n (SheafOfModules.unit X.ringCatSheaf)).toSubmodule.obj
        (op W.1) := by
      refine le_idealPowerMultiple_obj I n (SheafOfModules.unit X.ringCatSheaf) W ?_
      have h1 : r • (1 : Γ(X, W.1)) ∈ I.ideal W ^ n • (⊤ : Submodule Γ(X, W.1) Γ(X, W.1)) :=
        Submodule.smul_mem_smul hr Submodule.mem_top
      have h2 : r • (1 : Γ(X, W.1)) = r := mul_one r
      rw [h2] at h1
      exact h1
    let a : (idealPowerSheaf I n).val.obj (op W.1) := ⟨r, hr'⟩
    exact ⟨toTensorSheafSection X.toRingedSpace M (idealPowerSheaf I n) (op W.1)
      (m ⊗ₜ[X.presheaf.obj (op W.1)] a),
      idealPowerTensorMulAmbient_app_toTensorSheafSection I n M W.1 m a⟩
  · rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    exact ⟨s + t, (map_add _ s t).trans (congrArg₂ (· + ·) hs ht)⟩

end AffineSections

/-! ### On an affine scheme, the multiplication map is an isomorphism for flat modules -/

section Affine

variable {R : CommRingCat.{u}} (J : (Spec R).IdealSheafData) (n : ℕ)

/-- The structure sheaf `𝒪_{Spec R}`, read in `(Spec R).Modules`. -/
private abbrev specUnit : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf

/-- The inclusion `𝓘^n ⟶ 𝒪_{Spec R}`, read in `(Spec R).Modules`. -/
private abbrev idealPowerSheafι : idealPowerSheaf J n ⟶ (specUnit : (Spec R).Modules) :=
  (idealPowerMultiple J n (SheafOfModules.unit (Spec R).ringCatSheaf)).ι

/-- The inclusion `𝓘^n 𝓖 ⟶ 𝓖`, read in `(Spec R).Modules`. -/
private abbrev idealPowerObjι (G : (Spec R).Modules) :
    ((idealPowerMultiple J n G).toSheafOfModules : (Spec R).Modules) ⟶ G :=
  (idealPowerMultiple J n G).ι

/-- The multiplication map `𝓖 ⊗ 𝓘^n ⟶ 𝓘^n 𝓖`, with its source retyped as
`AlgebraicGeometry.TildeTensor.modTensor`. -/
private abbrev specIdealPowerTensorMul (G : (Spec R).Modules) :
    TildeTensor.modTensor G (idealPowerSheaf J n) ⟶
      ((idealPowerMultiple J n G).toSheafOfModules : (Spec R).Modules) :=
  idealPowerTensorMul J n G

/-- `m ⊗ a ↦ a • m`, with its source retyped as `AlgebraicGeometry.TildeTensor.modTensor`. -/
private abbrev specIdealPowerTensorMulAmbient (G : (Spec R).Modules) :
    TildeTensor.modTensor G (idealPowerSheaf J n) ⟶ G :=
  idealPowerTensorMulAmbient J n G

/-- `TildeTensor.gammaMap` is functorial. -/
private lemma gammaMap_comp {F F' F'' : (Spec R).Modules} (φ : F ⟶ F') (ψ : F' ⟶ F'')
    (y : Γ(F, ⊤)) :
    TildeTensor.gammaMap (φ ≫ ψ) y = TildeTensor.gammaMap ψ (TildeTensor.gammaMap φ y) :=
  DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (moduleSpecΓFunctor.map_comp φ ψ)) y

private lemma gammaMap_idealPowerTensorMul_ι (G : (Spec R).Modules)
    (y : Γ(TildeTensor.modTensor G (idealPowerSheaf J n), ⊤)) :
    TildeTensor.gammaMap (idealPowerObjι J n G)
        (TildeTensor.gammaMap (specIdealPowerTensorMul J n G) y) =
      TildeTensor.gammaMap (specIdealPowerTensorMulAmbient J n G) y := by
  have h : specIdealPowerTensorMul J n G ≫ idealPowerObjι J n G =
      specIdealPowerTensorMulAmbient J n G := idealPowerTensorMul_ι J n G
  rw [← h]
  exact (gammaMap_comp _ _ y).symm

/-- The tensor product of the identity of `𝓖` with the inclusion `𝓘^n ⟶ 𝒪`, retyped. -/
private abbrev specTensorι (G : (Spec R).Modules) :
    TildeTensor.modTensor G (idealPowerSheaf J n) ⟶ TildeTensor.modTensor G specUnit :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨(Spec R).presheaf, (Spec R).IsSheaf⟩ :
        Sheaf (JX (Spec R).toRingedSpace) CommRingCat.{u}))).map
    (X := (G, idealPowerSheaf J n)) (Y := (G, specUnit)) (𝟙 _, idealPowerSheafι J n)

/-- The right unitor `𝓖 ⊗ 𝒪 ≅ 𝓖`, retyped. -/
private abbrev specUnitor (G : (Spec R).Modules) :
    TildeTensor.modTensor G specUnit ⟶ G :=
  (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso (Spec R).toRingedSpace G).hom

private lemma specIdealPowerTensorMulAmbient_eq (G : (Spec R).Modules) :
    specIdealPowerTensorMulAmbient J n G = specTensorι J n G ≫ specUnitor G := rfl

private lemma gammaMap_idealPowerTensorMulAmbient (G : (Spec R).Modules)
    (x : Γ(G, ⊤) ⊗[R] Γ(idealPowerSheaf J n, ⊤)) :
    TildeTensor.gammaMap (specIdealPowerTensorMulAmbient J n G)
        (TildeTensor.gammaTensorMap G (idealPowerSheaf J n) x) =
      TildeTensor.gammaMap (specUnitor G)
        (TildeTensor.gammaTensorMap G specUnit
          ((TildeTensor.gammaMap (idealPowerSheafι J n)).lTensor Γ(G, ⊤) x)) := by
  have hid : TildeTensor.gammaMap (𝟙 G) = LinearMap.id := by
    unfold TildeTensor.gammaMap
    rw [CategoryTheory.Functor.map_id]
    rfl
  have h := TildeTensor.gammaTensorMap_naturality (𝟙 G) (idealPowerSheafι J n) x
  rw [hid] at h
  rw [specIdealPowerTensorMulAmbient_eq]
  refine (gammaMap_comp (specTensorι J n G) (specUnitor G) _).trans ?_
  exact congrArg (TildeTensor.gammaMap (specUnitor G)) h

/-- **On `Spec R`, the multiplication map `𝓖 ⊗ 𝓘^n ⟶ 𝓘^n 𝓖` is an isomorphism for a
quasi-coherent `𝓖` with flat global sections.** On global sections the source is
`Γ(𝓖) ⊗_R Γ(𝓘^n)` (the tensor half of Stacks 01I8), and the multiplication map into `Γ(𝓖)`
factors as `Γ(𝓖) ⊗_R Γ(𝓘^n) ⟶ Γ(𝓖) ⊗_R Γ(𝒪) ≅ Γ(𝓖)`, whose first factor is injective by
flatness; it is onto `Γ(𝓘^n 𝓖)` by `AlgebraicGeometry.exists_idealPowerTensorMulAmbient_app_eq`.
A morphism of quasi-coherent modules on an affine scheme which is bijective on global sections is
an isomorphism. -/
public theorem isIso_idealPowerTensorMul_of_flat (G : (Spec R).Modules) [G.IsQuasicoherent]
    (hG : Module.Flat R Γ(G, ⊤)) : IsIso (idealPowerTensorMul J n G) := by
  have hu : (specUnit : (Spec R).Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit
  have h𝓘 : (idealPowerSheaf J n).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple J n _
  have hS : ((idealPowerMultiple J n G).toSheafOfModules : (Spec R).Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple J n G
  have hT : (TildeTensor.modTensor G (idealPowerSheaf J n)).IsQuasicoherent :=
    @AlgebraicGeometry.tensorSheaf_isQuasicoherent (Spec R).toRingedSpace G
      (idealPowerSheaf J n) ‹_› ‹_›
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ
    (specIdealPowerTensorMul J n G) ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (TildeTensor.gammaMap (specIdealPowerTensorMul J n G))
  let L1 := TildeTensor.gammaTensorMap G (idealPowerSheaf J n)
  let L2 := TildeTensor.gammaMap (specIdealPowerTensorMul J n G)
  let L3 := TildeTensor.gammaMap (idealPowerObjι J n G)
  have hL3 : Function.Injective L3 := fun x y h => Subtype.val_injective h
  have hL1 : Function.Bijective L1 := TildeTensor.bijective_gammaTensorMap G _
  have hLt : Function.Injective ((TildeTensor.gammaMap (idealPowerSheafι J n)).lTensor Γ(G, ⊤)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Γ(G, ⊤))
      (TildeTensor.gammaMap (idealPowerSheafι J n)) (fun x y h => Subtype.val_injective h)
  have hL0 : Function.Injective (TildeTensor.gammaTensorMap G specUnit) :=
    (TildeTensor.bijective_gammaTensorMap G specUnit).1
  have hLu : Function.Injective (TildeTensor.gammaMap (specUnitor G)) :=
    (@TildeTensor.bijective_gammaMap R _ _ _ (TildeTensor.isIso_specModules (Iso.isIso_hom
      (AlgebraicGeometry.SheafOfModules.tensorSheafUnitRightIso (Spec R).toRingedSpace G)))).1
  have hkey : ∀ x, L3 (L2 (L1 x)) = TildeTensor.gammaMap (specUnitor G)
      (TildeTensor.gammaTensorMap G specUnit
        ((TildeTensor.gammaMap (idealPowerSheafι J n)).lTensor Γ(G, ⊤) x)) := fun x =>
    (gammaMap_idealPowerTensorMul_ι J n G (L1 x)).trans
      (gammaMap_idealPowerTensorMulAmbient J n G x)
  refine (Function.Bijective.of_comp_iff L2 hL1).mp ⟨fun x y h => ?_, fun y => ?_⟩
  · refine hLt (hL0 (hLu ?_))
    rw [← hkey, ← hkey]
    exact congrArg L3 h
  · obtain ⟨s, hs⟩ := exists_idealPowerTensorMulAmbient_app_eq J n G
      ⟨⊤, isAffineOpen_top (Spec R)⟩ (L3 y) y.2
    obtain ⟨x, rfl⟩ := hL1.2 s
    exact ⟨x, hL3 ((gammaMap_idealPowerTensorMul_ι J n G (L1 x)).trans hs)⟩

/-- **The ideal of global sections** of a quasi-coherent sheaf of ideals `𝓘` on `Spec R`: the
ideal `I ⊆ R` corresponding to `𝓘(Spec R) ⊆ Γ(Spec R, 𝒪)` under `R ≅ Γ(Spec R, 𝒪)`. -/
private def globalIdeal : Ideal R :=
  (J.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩).comap (Scheme.ΓSpecIso R).inv.hom

/-- The scalar of `Γ(Spec R, 𝒪)` through which `r : R` acts on global sections is the image of
`r` under `R ≅ Γ(Spec R, 𝒪)`. -/
private lemma cTop_eq (r : R) : TildeTensor.cTop r = (Scheme.ΓSpecIso R).inv.hom r := by
  unfold TildeTensor.cTop
  have h : (Opens.leTop (⊤ : (Spec R).Opens)).op = 𝟙 (op (⊤ : (Spec R).Opens)) :=
    Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id]
  rfl

/-- The image of `globalIdeal J ^ k` in `Γ(Spec R, 𝒪)` is `𝓘(Spec R) ^ k`. -/
private lemma map_globalIdeal_pow (k : ℕ) :
    (globalIdeal J ^ k).map (Scheme.ΓSpecIso R).inv.hom =
      J.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ ^ k := by
  have hs : Function.Surjective (Scheme.ΓSpecIso R).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2
  rw [Ideal.map_pow, globalIdeal, Ideal.map_comap_of_surjective _ hs]

/-- An element of `globalIdeal J ^ k` acts on global sections through an element of
`𝓘(Spec R) ^ k`. -/
private lemma cTop_mem_pow (k : ℕ) (a : R) (ha : a ∈ globalIdeal J ^ k) :
    TildeTensor.cTop a ∈ J.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ ^ k := by
  rw [cTop_eq, ← map_globalIdeal_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- Every element of `𝓘(Spec R) ^ k` is the scalar of an element of `globalIdeal J ^ k`. -/
private lemma exists_cTop_eq (k : ℕ) (r : Γ(Spec R, ⊤))
    (hr : r ∈ J.ideal ⟨⊤, isAffineOpen_top (Spec R)⟩ ^ k) :
    ∃ a ∈ globalIdeal J ^ k, TildeTensor.cTop a = r := by
  have hs : Function.Surjective (Scheme.ΓSpecIso R).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).2
  rw [← map_globalIdeal_pow, Ideal.mem_map_iff_of_surjective _ hs] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact ⟨a, ha, cTop_eq a⟩

section TildeIdealPower

variable (k : ℕ) {A B : ModuleCat.{u} R} (g : A ⟶ B)

/-- The canonical global section of `B̃` attached to an element of `I^k B` is a section of
`𝓘^k B̃`. -/
private lemma topSec_mem_idealPowerMultiple (b : B)
    (hb : b ∈ globalIdeal J ^ k • (⊤ : Submodule R B)) :
    TildeTensor.topSec B b ∈ (idealPowerMultiple J k (tilde B)).toSubmodule.obj (op ⊤) := by
  refine Submodule.smul_induction_on hb (fun a ha b _ => ?_) (fun x y hx hy => ?_)
  · rw [TildeTensor.topSec_smul]
    exact le_idealPowerMultiple_obj J k (tilde B) ⟨⊤, isAffineOpen_top (Spec R)⟩
      (Submodule.smul_mem_smul (cTop_mem_pow J k a ha) Submodule.mem_top)
  · rw [TildeTensor.topSec_add]
    exact add_mem hx hy

/-- Conversely every global section of `𝓘^k B̃` is the canonical section of an element of
`I^k B`. -/
private lemma exists_topSec_eq (z : Γ(tilde B, ⊤))
    (hz : z ∈ (idealPowerMultiple J k (tilde B)).toSubmodule.obj (op ⊤)) :
    ∃ b ∈ globalIdeal J ^ k • (⊤ : Submodule R B), TildeTensor.topSec B b = z := by
  rw [Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple J k (tilde B)
    ⟨⊤, isAffineOpen_top (Spec R)⟩] at hz
  have hsurj : Function.Surjective (TildeTensor.topSec B) :=
    (ConcreteCategory.bijective_of_isIso (tilde.toOpen B ⊤)).2
  refine Submodule.smul_induction_on hz (fun r hr z _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨a, ha, rfl⟩ := exists_cTop_eq J k r hr
    obtain ⟨b, rfl⟩ := hsurj z
    exact ⟨a • b, Submodule.smul_mem_smul ha Submodule.mem_top, TildeTensor.topSec_smul B a b⟩
  · obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨b + b', add_mem hb hb', TildeTensor.topSec_add B b b'⟩

/-- `f ↦ f̃` on global sections: the adjoint of `tilde.map g` is `g` followed by the canonical
global sections. -/
private lemma tildeAdjoint_apply (a : A) :
    ((tilde.adjunction.homEquiv A (tilde B)) (tilde.map g)).hom a = TildeTensor.topSec B (g a) :=
  (congrArg (fun φ : A ⟶ moduleSpecΓFunctor.obj (tilde B) => φ.hom a)
    (tilde.adjunction.homEquiv_unit A (tilde B) (tilde.map g))).trans
    (TildeTensor.toOpen_map_app_apply g ⊤ a)

/-- The global sections of `𝓘^k B̃ ⟶ B̃` are injective. -/
private lemma injective_gammaMap_ι :
    Function.Injective (moduleSpecΓFunctor.map
      (idealPowerMultiple J k (tilde B)).ι).hom :=
  fun _ _ h => Subtype.val_injective h

variable {k g} in
/-- For `g : A ⟶ B` with image in `I^k B`, the morphism `A ⟶ Γ(𝓘^k B̃)` it induces. -/
private def tildeIdealPowerSections
    (hg : LinearMap.range g.hom ≤ globalIdeal J ^ k • (⊤ : Submodule R B)) :
    A ⟶ moduleSpecΓFunctor.obj
      ((idealPowerMultiple J k (tilde B)).toSheafOfModules : (Spec R).Modules) :=
  let L3 := (moduleSpecΓFunctor.map (idealPowerMultiple J k (tilde B)).ι).hom
  let f0 := ((tilde.adjunction.homEquiv A (tilde B)) (tilde.map g)).hom
  have hf0 : ∀ a, f0 a ∈ LinearMap.range L3 := fun a =>
    ⟨(⟨f0 a, (tildeAdjoint_apply g a).symm ▸
        topSec_mem_idealPowerMultiple J k (g a) (hg (LinearMap.mem_range_self _ a))⟩ :
      ↥((idealPowerMultiple J k (tilde B)).toSubmodule.obj (op ⊤))), rfl⟩
  ModuleCat.homEquiv.symm ((LinearEquiv.ofInjective L3 (injective_gammaMap_ι J k)).symm.toLinearMap
    ∘ₗ f0.codRestrict (LinearMap.range L3) hf0)

variable {k g} in
private lemma tildeIdealPowerSections_comp
    (hg : LinearMap.range g.hom ≤ globalIdeal J ^ k • (⊤ : Submodule R B)) :
    tildeIdealPowerSections J hg ≫ moduleSpecΓFunctor.map (idealPowerMultiple J k (tilde B)).ι =
      (tilde.adjunction.homEquiv A (tilde B)) (tilde.map g) := by
  ext a
  exact LinearEquiv.ofInjective_symm_apply (h := injective_gammaMap_ι J k) _ _

variable {k g} in
/-- For `g : A ⟶ B` with image in `I^k B`, the morphism `Ã ⟶ 𝓘^k B̃` through which `g̃` factors. -/
private def tildeIdealPowerHom
    (hg : LinearMap.range g.hom ≤ globalIdeal J ^ k • (⊤ : Submodule R B)) :
    tilde A ⟶ ((idealPowerMultiple J k (tilde B)).toSheafOfModules : (Spec R).Modules) :=
  (tilde.adjunction.homEquiv A _).symm (tildeIdealPowerSections J hg)

variable {k g} in
private lemma tildeIdealPowerHom_ι
    (hg : LinearMap.range g.hom ≤ globalIdeal J ^ k • (⊤ : Submodule R B)) :
    tildeIdealPowerHom J hg ≫ (idealPowerMultiple J k (tilde B)).ι = tilde.map g :=
  (tilde.adjunction.homEquiv A (tilde B)).injective <|
    (tilde.adjunction.homEquiv_naturality_right _ _).trans
      ((congrArg (· ≫ moduleSpecΓFunctor.map (idealPowerMultiple J k (tilde B)).ι)
        (Equiv.apply_symm_apply _ _)).trans (tildeIdealPowerSections_comp J hg))

variable {k g} in
/-- For an injective `g : A ⟶ B` with image `I^k B`, the morphism `Ã ⟶ 𝓘^k B̃` is an
isomorphism: on global sections it is `A ≅ I^k B = Γ(𝓘^k B̃)`. -/
private lemma isIso_tildeIdealPowerHom (hinj : Function.Injective g.hom)
    (hrange : LinearMap.range g.hom = globalIdeal J ^ k • (⊤ : Submodule R B)) :
    IsIso (tildeIdealPowerHom J hrange.le) := by
  have : ((idealPowerMultiple J k (tilde B)).toSheafOfModules :
      (Spec R).Modules).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.IdealPowerComparison.isQuasicoherent_idealPowerMultiple J k _
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_moduleSpecΓ _ ?_
  let h := tildeIdealPowerSections J hrange.le
  have e : tilde.adjunction.unit.app A ≫ moduleSpecΓFunctor.map (tildeIdealPowerHom J hrange.le) =
      h :=
    (tilde.adjunction.homEquiv_unit A _ (tildeIdealPowerHom J hrange.le)).symm.trans
      (Equiv.apply_symm_apply _ _)
  have hcomp : ∀ a, (moduleSpecΓFunctor.map (idealPowerMultiple J k (tilde B)).ι).hom (h.hom a) =
      TildeTensor.topSec B (g a) := fun a =>
    (congrArg (fun φ : A ⟶ moduleSpecΓFunctor.obj (tilde B) => φ.hom a)
      (tildeIdealPowerSections_comp J hrange.le)).trans (tildeAdjoint_apply g a)
  have htop : Function.Bijective (TildeTensor.topSec B) :=
    ConcreteCategory.bijective_of_isIso (tilde.toOpen B ⊤)
  have hh : IsIso h := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a a' haa => hinj (htop.1 ?_), fun y => ?_⟩
    · rw [← hcomp, ← hcomp]
      exact congrArg _ haa
    · obtain ⟨b, hb, hby⟩ := exists_topSec_eq J k _ y.2
      rw [← hrange] at hb
      obtain ⟨a, rfl⟩ := hb
      exact ⟨a, injective_gammaMap_ι J k ((hcomp a).trans hby)⟩
  have hc : IsIso (tilde.adjunction.unit.app A ≫
      moduleSpecΓFunctor.map (tildeIdealPowerHom J hrange.le)) := by
    rw [e]
    exact hh
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (tilde.adjunction.unit.app A)
    (moduleSpecΓFunctor.map (tildeIdealPowerHom J hrange.le)) inferInstance hc

end TildeIdealPower

section TildeImage

open Stacks.AdicSystem.IdealPowerTensorComparison

variable (N : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)

private lemma range_image_ι_f :
    LinearMap.range ((image.ι (idealPowerMultiplication N (globalIdeal J) n)).f i).hom =
      globalIdeal J ^ (n + 1) • (⊤ : Submodule R (N.X i)) := by
  rw [← range_idealPowerMultiplication_f]
  have hfac : ((idealPowerMultiplication N (globalIdeal J) n).f i).hom =
      ((image.ι (idealPowerMultiplication N (globalIdeal J) n)).f i).hom ∘ₗ
        ((factorThruImage (idealPowerMultiplication N (globalIdeal J) n)).f i).hom :=
    congrArg (fun φ => (φ.f i).hom)
      (image.fac (idealPowerMultiplication N (globalIdeal J) n)).symm
  have hsurj : Function.Surjective
      ((factorThruImage (idealPowerMultiplication N (globalIdeal J) n)).f i).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  rw [hfac, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]

private lemma injective_image_ι_f :
    Function.Injective ((image.ι (idealPowerMultiplication N (globalIdeal J) n)).f i).hom :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

/-- **The associated sheaf of `I^{n+1} N^i` is `𝓘^{n+1} Ñ^i`**, for the ideal of global sections
`I` of `𝓘`. -/
private def tildeIdealPowerIso :
    tilde ((idealPowerComplex N (globalIdeal J) n).X i) ≅
      ((idealPowerMultiple J (n + 1) (tilde (N.X i))).toSheafOfModules : (Spec R).Modules) :=
  @asIso _ _ _ _ (tildeIdealPowerHom J (range_image_ι_f J n N i).le)
    (isIso_tildeIdealPowerHom J (injective_image_ι_f J n N i) (range_image_ι_f J n N i))

private lemma tildeIdealPowerIso_hom_ι :
    (tildeIdealPowerIso J n N i).hom ≫ (idealPowerMultiple J (n + 1) (tilde (N.X i))).ι =
      tilde.map ((image.ι (idealPowerMultiplication N (globalIdeal J) n)).f i) :=
  tildeIdealPowerHom_ι J _

/-- The complex of sheaves associated to a complex of `R`-modules. -/
private abbrev tildeC (N : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex (Spec R).Modules ℤ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj N

/-- **The associated complex of `I^{n+1} N` is `𝓘^{n+1} Ñ`.** -/
private def tildeIdealPowerComplexIso :
    tildeC (idealPowerComplex N (globalIdeal J) n) ≅
      (idealPowerComplexSystem J (tildeC N)).complex (n + 1) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => tildeIdealPowerIso J n N i) fun i j _ => by
    refine cancel_sheafSubmodule_ι (idealPowerMultiple J (n + 1) (tilde (N.X j))) _ _ ?_
    have hc := ((idealPowerComplexSystem J (tildeC N)).inclusion (n + 1)).comm i j
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((tildeIdealPowerIso J n N i).hom ≫ ·) hc.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ tilde.map (N.d i j)) (tildeIdealPowerIso_hom_ι J n N i)).trans ?_
    refine (tilde.map_comp _ _).symm.trans ?_
    refine (congrArg tilde.map
      ((image.ι (idealPowerMultiplication N (globalIdeal J) n)).comm i j)).trans ?_
    refine (tilde.map_comp _ _).trans ?_
    refine (congrArg (tilde.map _ ≫ ·) (tildeIdealPowerIso_hom_ι J n N j).symm).trans ?_
    exact (Category.assoc _ _ _).symm

private lemma tildeIdealPowerComplexIso_hom_inclusion :
    (tildeIdealPowerComplexIso J n N).hom ≫
        (idealPowerComplexSystem J (tildeC N)).inclusion (n + 1) =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (image.ι (idealPowerMultiplication N (globalIdeal J) n)) := by
  ext i : 1
  exact tildeIdealPowerIso_hom_ι J n N i

private lemma mono_idealPowerComplexSystem_inclusion (F : CochainComplex (Spec R).Modules ℤ)
    (m : ℕ) : Mono ((idealPowerComplexSystem J F).inclusion m) :=
  HomologicalComplex.mono_of_mono_f _ fun i =>
    SheafOfModules.Submodule.instMonoι (idealPowerMultiple J m (F.X i))

variable {N} in
/-- The identification `(I^{n+1} N)~ ≅ 𝓘^{n+1} Ñ` is natural in `N`. -/
private lemma tildeIdealPowerComplexIso_naturality {M : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : N ⟶ M) :
    (tildeIdealPowerComplexIso J n N).hom ≫
        DeligneTriangle.idealPowerComplexMap J
          (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map p) (n + 1) =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (idealPowerComplexMap p (globalIdeal J) n) ≫ (tildeIdealPowerComplexIso J n M).hom := by
  have := mono_idealPowerComplexSystem_inclusion J (tildeC M) (n + 1)
  let T := (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)
  apply (cancel_mono ((idealPowerComplexSystem J (tildeC M)).inclusion (n + 1))).1
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (DeligneTriangle.idealPowerComplexMap_comp_inclusion J (T.map p)
    (n + 1))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ T.map p) (tildeIdealPowerComplexIso_hom_inclusion J n N)).trans ?_
  refine (T.map_comp _ _).symm.trans ?_
  refine (congrArg T.map (idealPowerComplexMap_comp p (globalIdeal J) n).symm).trans ?_
  refine (T.map_comp _ _).trans ?_
  refine (congrArg (T.map _ ≫ ·) (tildeIdealPowerComplexIso_hom_inclusion J n M).symm).trans ?_
  exact (Category.assoc _ _ _).symm

/-- The identification `(I^{n+1} N)~ ≅ 𝓘^{n+1} Ñ` commutes with the transitions. -/
private lemma tildeIdealPowerComplexIso_transition :
    (tildeIdealPowerComplexIso J (n + 1) N).hom ≫
        (idealPowerComplexSystem J (tildeC N)).transition (n + 1) =
      ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (idealPowerComplexTransition N (globalIdeal J) n) ≫
        (tildeIdealPowerComplexIso J n N).hom := by
  have := mono_idealPowerComplexSystem_inclusion J (tildeC N) (n + 1)
  let T := (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)
  apply (cancel_mono ((idealPowerComplexSystem J (tildeC N)).inclusion (n + 1))).1
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) ((idealPowerComplexSystem J (tildeC N)).transition_include
    (n + 1))).trans ?_
  refine (tildeIdealPowerComplexIso_hom_inclusion J (n + 1) N).trans ?_
  refine (congrArg T.map (idealPowerComplexTransition_comp N (globalIdeal J) n).symm).trans ?_
  refine (T.map_comp _ _).trans ?_
  refine (congrArg (T.map _ ≫ ·) (tildeIdealPowerComplexIso_hom_inclusion J n N).symm).trans ?_
  exact (Category.assoc _ _ _).symm

end TildeImage

section Derived

open Stacks.AdicSystem.IdealPowerTensorComparison

variable (N : CochainComplex (ModuleCat.{u} R) ℤ)

/-- Derived sheafification carries the inverse system `(I^{n+1} N)_n` of `D(R)` to the inverse
system `(𝓘^{n+1} Ñ)_n` of `D(𝒪_{Spec R})`. -/
private def tildeIdealPowerSystemHom :
    Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerSystem N (globalIdeal J)
        (idealPowerComplexTransition N (globalIdeal J)) ⋙
        (tilde.functor R).mapDerivedCategory ⟶
      Stacks.AdicSystem.DerivedReductionProIso.successorOp ⋙
        (DeligneTriangle.idealPowerComplexFunctor J (tildeC N) ⋙ DerivedCategory.Q) :=
  NatTrans.ofOpSequence
    (fun n => (tilde.functor R).mapDerivedCategoryFactors.hom.app
        (idealPowerComplex N (globalIdeal J) n) ≫
      DerivedCategory.Q.map (tildeIdealPowerComplexIso J n N).hom)
    (fun n => by
      let T := (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)
      let fac := (tilde.functor R).mapDerivedCategoryFactors.hom
      have h1 : (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerSystem N (globalIdeal J)
          (idealPowerComplexTransition N (globalIdeal J))
          ⋙ (tilde.functor R).mapDerivedCategory).map (homOfLE (Nat.le_succ n)).op =
          (tilde.functor R).mapDerivedCategory.map
            (DerivedCategory.Q.map (idealPowerComplexTransition N (globalIdeal J) n)) :=
        congrArg (tilde.functor R).mapDerivedCategory.map
          (Functor.ofOpSequence_map_homOfLE_succ _ n)
      have h2 : (Stacks.AdicSystem.DerivedReductionProIso.successorOp ⋙
          (DeligneTriangle.idealPowerComplexFunctor J (tildeC N) ⋙ DerivedCategory.Q)).map
            (homOfLE (Nat.le_succ n)).op =
          DerivedCategory.Q.map ((idealPowerComplexSystem J (tildeC N)).transition (n + 1)) :=
        congrArg DerivedCategory.Q.map (Functor.ofOpSequence_map_homOfLE_succ
          (fun m => (idealPowerComplexSystem J (tildeC N)).transition m) (n + 1))
      rw [h1, h2]
      exact comp_comp_eq_of_naturality DerivedCategory.Q
        (tildeIdealPowerComplexIso_transition J n N)
        (fac.naturality (idealPowerComplexTransition N (globalIdeal J) n)))

private lemma tildeIdealPowerSystemHom_app (n : ℕ) :
    (tildeIdealPowerSystemHom J N).app (op n) =
      (tilde.functor R).mapDerivedCategoryFactors.hom.app (idealPowerComplex N (globalIdeal J) n) ≫
        DerivedCategory.Q.map (tildeIdealPowerComplexIso J n N).hom :=
  NatTrans.ofOpSequence_app _ _ (op n)

private lemma isIso_tildeIdealPowerSystemHom_app (n : ℕ) :
    IsIso ((tildeIdealPowerSystemHom J N).app (op n)) := by
  rw [tildeIdealPowerSystemHom_app]
  exact (((tilde.functor R).mapDerivedCategoryFactors.app _) ≪≫
    DerivedCategory.Q.mapIso (tildeIdealPowerComplexIso J n N)).isIso_hom

variable {N} in
private lemma tildeIdealPowerSystemHom_comm {M : CochainComplex (ModuleCat.{u} R) ℤ}
    (p : N ⟶ M) :
    Functor.whiskerRight (idealPowerSystemMap p (globalIdeal J))
        (tilde.functor R).mapDerivedCategory ≫ tildeIdealPowerSystemHom J M =
      tildeIdealPowerSystemHom J N ≫
        Functor.whiskerLeft Stacks.AdicSystem.DerivedReductionProIso.successorOp
          (Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans J
            (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map p))
            DerivedCategory.Q) := by
  ext ⟨n⟩
  let fac := (tilde.functor R).mapDerivedCategoryFactors.hom
  refine ((NatTrans.comp_app _ _ _).trans ?_).trans (NatTrans.comp_app _ _ _).symm
  rw [tildeIdealPowerSystemHom_app, tildeIdealPowerSystemHom_app]
  exact comp_comp_eq_of_naturality DerivedCategory.Q (tildeIdealPowerComplexIso_naturality J n p)
    (fac.naturality (idealPowerComplexMap p (globalIdeal J) n))

/-- **Transport of the algebraic pro-isomorphism.** If the maps `I^{n+1} P ⟶ I^{n+1} M` induced
by `p : P ⟶ M` have pro-inverses in `D(R)`, then the maps `𝓘^n P̃ ⟶ 𝓘^n M̃` have pro-inverses in
`D(𝒪_{Spec R})`. -/
private lemma hasProInv_idealPowerComplexMapNatTrans_tilde
    {P M : CochainComplex (ModuleCat.{u} R) ℤ} (p : P ⟶ M)
    (halg : HasProInv (idealPowerSystemMap p (globalIdeal J))) :
    HasProInv (Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans J
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).map p))
        DerivedCategory.Q) := by
  apply hasProInv_of_whiskerLeft_successor
  have : ∀ X, IsIso ((tildeIdealPowerSystemHom J P).app X) := fun X =>
    isIso_tildeIdealPowerSystemHom_app J P X.unop
  have : ∀ X, IsIso ((tildeIdealPowerSystemHom J M).app X) := fun X =>
    isIso_tildeIdealPowerSystemHom_app J M X.unop
  have := NatIso.isIso_of_isIso_app (tildeIdealPowerSystemHom J P)
  have := NatIso.isIso_of_isIso_app (tildeIdealPowerSystemHom J M)
  refine CategoryTheory.ProSeq.proInverse_of_natIso _ _
    (asIso (tildeIdealPowerSystemHom J P)).symm (asIso (tildeIdealPowerSystemHom J M)).symm ?_
    (hasProInv_whiskerRight halg (tilde.functor R).mapDerivedCategory)
  refine Eq.symm ((Iso.inv_comp_eq _).2 ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  exact ((Iso.eq_comp_inv _).2 (tildeIdealPowerSystemHom_comm J p))

end Derived

section Main

open Stacks.AdicSystem.IdealPowerTensorComparison

private lemma idealPowerComplexMapNatTrans_comp {F G H : CochainComplex (Spec R).Modules ℤ}
    (f : F ⟶ G) (g : G ⟶ H) :
    Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans J (f ≫ g))
        DerivedCategory.Q =
      Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans J f) DerivedCategory.Q ≫
        Functor.whiskerRight (DeligneTriangle.idealPowerComplexMapNatTrans J g)
          DerivedCategory.Q := by
  ext ⟨n⟩
  refine (congrArg DerivedCategory.Q.map
    (((DeligneTriangle.idealPowerFunctor J n).mapHomologicalComplex
      (ComplexShape.up ℤ)).map_comp f g)).trans (DerivedCategory.Q.map_comp _ _)

/-- The complex of sheaves associated to a bounded-above complex of finite free modules computes
the canonical maps: they are isomorphisms. -/
private lemma isIso_derivedTensorIdealPowerMap_tilde (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hPK : CochainComplex.KFlat.{u, u} P) (hP : ∀ i, Module.Flat R (P.X i)) (n : ℕ) :
    IsIso ((derivedTensorIdealPowerNatTrans J (tildeC P)).app (op n)) := by
  rw [derivedTensorIdealPowerNatTrans_app]
  refine isIso_derivedTensorIdealPowerMap_of_kFlat J (tildeC P) (kFlat_tilde P hPK) n ?_
  have hrow : IsIso (idealPowerRowMap J n (tildeC P)) := by
    have : ∀ i, IsIso ((idealPowerRowMap J n (tildeC P)).f i) := fun i =>
      have := hP i
      isIso_idealPowerTensorMul_of_flat J n (tilde (P.X i))
        (Module.Flat.of_linearEquiv (TildeTensor.topEquiv (P.X i)).symm)
    exact HomologicalComplex.Hom.isIso_of_components _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (CochainComplex.KFlatBifunctor.totalSingleIso _ _ _).isIso_hom hrow

end Main

end Affine

open Stacks.AdicSystem.IdealPowerTensorComparison in
/-- **Stacks 0G4U on an affine Noetherian scheme.** Let `R` be a Noetherian ring, `𝓘` a
quasi-coherent sheaf of ideals on `Spec R` and `𝓕^•` a bounded complex of coherent
`𝒪_{Spec R}`-modules. Then the canonical maps `𝓕^• ⊗^L 𝓘^n ⟶ 𝓘^n 𝓕^•` of
`AlgebraicGeometry.derivedTensorIdealPowerNatTrans` have pro-inverses in `D(𝒪_{Spec R})`: each
level acquires a two-sided inverse after passing to a later level. -/
public theorem proInverse_derivedTensorIdealPowerNatTrans_spec (R : CommRingCat.{u})
    [IsNoetherianRing R] (J : (Spec R).IdealSheafData) (F : CochainComplex (Spec R).Modules ℤ)
    (hcoh : ∀ i, (F.X i).IsCoherent) (hge : ∃ a, F.IsStrictlyGE a)
    (hle : ∃ b, F.IsStrictlyLE b) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : (Functor.ofOpSequence (idealPowerComplexSystem J F).transition ⋙
          DerivedCategory.Q).obj (op m) ⟶
        (derivedTensorIdealPowerSystem J (DerivedCategory.Q.obj F)).obj (op n)),
      (derivedTensorIdealPowerNatTrans J F).app (op m) ≫ s =
          (derivedTensorIdealPowerSystem J (DerivedCategory.Q.obj F)).map (homOfLE h).op ∧
        s ≫ (derivedTensorIdealPowerNatTrans J F).app (op n) =
          (Functor.ofOpSequence (idealPowerComplexSystem J F).transition ⋙
            DerivedCategory.Q).map (homOfLE h).op := by
  have hq : ∀ i, (F.X i).IsQuasicoherent := fun i =>
    have := hcoh i
    _root_.isQuasicoherent_of_isCoherent (F.X i)
  let M : CochainComplex (ModuleCat.{u} R) ℤ :=
    (moduleSpecΓFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj F
  let c : tildeC M ≅ F := Stacks.AffineTilde.tildeGammaComplexIso F fun i =>
    have := hq i
    inferInstance
  have hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b := by
    obtain ⟨a, ha⟩ := hge
    obtain ⟨b, hb⟩ := hle
    refine ⟨a, b, ?_, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      exact fun i hi => Functor.map_isZero (moduleSpecΓFunctor (R := R))
        (F.isZero_of_isStrictlyGE a i hi)
    · rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => Functor.map_isZero (moduleSpecΓFunctor (R := R))
        (F.isZero_of_isStrictlyLE b i hi)
  have hMfinite : ∀ i : ℤ, Module.Finite R (M.X i) := fun i =>
    have := hq i
    have := (hcoh i).isFiniteType
    Stacks.AlgebraicGeometry.PushforwardCoherent.finite_moduleSpecΓ (F.X i)
  obtain ⟨P, p, ⟨b, hPb⟩, hPfinite, hp, -, hpred⟩ :=
    Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction
      (globalIdeal J) M hMbounded hMfinite
  have hPflat : ∀ i, Module.Flat R (P.X i) := fun i =>
    have := (hPfinite i).2
    inferInstance
  have hPK : CochainComplex.KFlat.{u, u} P :=
    StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective P b fun i =>
      have := (hPfinite i).2
      inferInstance
  let T := (tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)
  let π : tildeC P ⟶ F := T.map p ≫ c.hom
  have hQp : IsIso (DerivedCategory.Q.map (T.map p)) := by
    let fac := (tilde.functor R).mapDerivedCategoryFactors.hom
    have hnat := fac.naturality p
    have := hp
    have h1 : IsIso (fac.app P ≫ DerivedCategory.Q.map (T.map p)) := by
      change IsIso (fac.app P ≫ (T ⋙ DerivedCategory.Q).map p)
      rw [← hnat]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _
        (Functor.map_isIso (F := (tilde.functor R).mapDerivedCategory)
          (f := DerivedCategory.Q.map p))
        ((tilde.functor R).mapDerivedCategoryFactors.app M).isIso_hom
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ (fac.app P) _
      ((tilde.functor R).mapDerivedCategoryFactors.app P).isIso_hom h1
  have hQπ : IsIso (DerivedCategory.Q.map π) := by
    have e : DerivedCategory.Q.map π =
        DerivedCategory.Q.map (T.map p) ≫ DerivedCategory.Q.map c.hom :=
      DerivedCategory.Q.map_comp _ _
    rw [e]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hQp inferInstance
  have key : HasProInv (derivedTensorIdealPowerNatTrans J F) := by
    refine proInverse_leftCancel (derivedTensorIdealPowerSystemMap J (DerivedCategory.Q.map π)) _
      (proInverse_of_isIso_app _ fun n => isIso_derivedTensorIdealPowerSystemMap_app J n
        (@asIso _ _ _ _ (DerivedCategory.Q.map π) hQπ)) ?_
    rw [derivedTensorIdealPowerNatTrans_naturality J π]
    refine proInverse_comp _ _ (proInverse_of_isIso_app _
      (isIso_derivedTensorIdealPowerMap_tilde J P hPK hPflat)) ?_
    rw [idealPowerComplexMapNatTrans_comp J (T.map p) c.hom]
    refine proInverse_comp _ _ (hasProInv_idealPowerComplexMapNatTrans_tilde J p
      (proInverse_idealPowerSystemMap_of_reduction p (globalIdeal J) hpred)) ?_
    refine proInverse_of_isIso_app _ fun n => ?_
    exact (DerivedCategory.Q.mapIso (((DeligneTriangle.idealPowerFunctor J n).mapHomologicalComplex
      (ComplexShape.up ℤ)).mapIso c)).isIso_hom
  exact key

end AlgebraicGeometry

end
