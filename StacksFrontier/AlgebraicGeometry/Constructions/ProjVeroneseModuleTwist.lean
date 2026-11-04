module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwistMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjShifted.Basic

/-!
# The Veronese comparison and the twisting of associated sheaves

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism and `M` a graded `S`-module, with `M' = M⁽ᵈ⁾`. Tag 0B5J's assertion (1) identifies
`M̃` with `i^*(M'~)`. Applied to the shift `M(nd)`, whose Veronese part is the shift `M'(n)`
(`Stacks.Veronese.veroneseModuleShiftEquiv`), it identifies `M(nd)~` with `i^*(M'(n)~)`, exactly
as assertion (2) is (1) at `S(nd)`. This file proves that these identifications are compatible
with the canonical maps `M̃ ⊗ 𝒪(a) ⟶ M(a)~`: the square

```
M̃ ⊗ 𝒪_X(nd) ─────────── canonical ───────────▸ M(nd)~
   │ (1) ⊗ (2)                                    │ (1) at M(nd), then M(nd)' = M'(n)
   ▾                                              ▾
i^*(M'~) ⊗ i^*𝒪'(n) ── 01CD⁻¹ ──▸ i^*(M'~ ⊗ 𝒪'(n)) ── i^* canonical ──▸ i^*(M'(n)~)
```

commutes. Both paths send `m / f^(pd)` and `a / f^(qd)` to the pullback of `am / (f ᵈ)^(p+q)`.

## Main definitions

* `Stacks.Veronese.veroneseShiftedSheafIso`: on `Proj S'`, `(M(nd)')~ ≅ (M'(n))~`.
* `Stacks.Veronese.veroneseShiftedModuleIso`: on `Proj S`, `M(nd)~ ≅ i^*(M'(n)~)`.
* `Stacks.Veronese.veroneseModuleTwistLeft` and `Stacks.Veronese.veroneseModuleTwistRight`: the
  two sides of the square.

## Main results

* `Stacks.Veronese.veroneseModuleTwistCompatibility`: the square commutes.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (tensorGrading shiftedGrading)
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading twistingSheaf)
open scoped TensorProduct

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

universe u v w

section Generic

variable {A M : Type u} {ς τ : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (ℳ : ℤ → τ) [Decomposition ℳ] [SetLike.GradedSMul 𝒜 ℳ]

/-- **The canonical map `M̃ ⊗ 𝒪(a) ⟶ M(a)~` on a chart.** Over `D₊(g)` it sends the pure tensor
of `m / g ᵏ` and `x / g ˡ` to `xm / g^(k+l)`. -/
public theorem moduleTwistMap_degreeZeroFraction (a : ℤ)
    {g : A} {c : ℕ} (hg : g ∈ 𝒜 c) (hc : 0 < c) (k l : ℕ) (m : M) (x : A)
    (hm : m ∈ ℳ (k • (c : ℤ)))
    (hx : x ∈ twistGrading (S := A) 𝒜 a (l • (c : ℤ)))
    (hxm : (TensorProduct.rid A M).toLinearMap (m ⊗ₜ x) ∈
      shiftedGrading ℳ a ((k + l) • (c : ℤ))) :
    ((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap 𝒜 ℳ a).val.app
        (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒜 ℳ) (twistingSheaf 𝒜 a)
          (op (ProjectiveSpectrum.basicOpen 𝒜 g))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 ℳ hg hc).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℳ hg k m hm) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
              (twistGrading (S := A) 𝒜 a) hg hc).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 a) hg l x
                hx))) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
          (shiftedGrading ℳ a) hg hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 (shiftedGrading ℳ a) hg
          (k + l) ((TensorProduct.rid A M).toLinearMap (m ⊗ₜ x)) hxm) := by
  let := tensorGrading_decomposition (S := A) 𝒜 ℳ (twistGrading (S := A) 𝒜 a)
  let := tensorGrading_gradedSMul (S := A) 𝒜 ℳ (twistGrading (S := A) 𝒜 a)
  change ((associatedModuleSheafMap 𝒜
      (tensorGrading ℳ (twistGrading (S := A) 𝒜 a))
      (shiftedGrading ℳ a) (TensorProduct.rid A M).toLinearMap
      (Stacks.GradedModule.rid_mem_shiftedGrading 𝒜 ℳ a)).val.app
        (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom
      (((associatedModuleSheafTensorMap 𝒜 ℳ
        (twistGrading (S := A) 𝒜 a)).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom _) = _
  rw [associatedModuleSheafTensorMap_standardOpen]
  exact associatedModuleSheafMap_degreeZeroFraction 𝒜 _ _ _ _ hg hc (k + l) _ _

end Generic

section AnyUniverse

variable {S : Type u} {M : Type v} {σ : Type w} [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- On `Proj S⁽ᵈ⁾` the sheaf associated to the Veronese part of the shift `M(nd)` is the sheaf
associated to the shift `M⁽ᵈ⁾(n)`: the associated-sheaf map of `veroneseModuleShiftEquiv`. -/
public noncomputable def veroneseShiftedSheafIso (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 (shiftedGrading 𝒨 (n * d)) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d) ≅
      ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 (shiftedGrading 𝒨 (n * d)) d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let sourceGrade := veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d
  let targetGrade := shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n
  let e := veroneseModuleShiftEquiv 𝒮 𝒨 d n
  have hφ := veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n
  have hsymm := veroneseModuleShiftEquiv_symm_mem 𝒮 𝒨 d n
  let f := associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade targetGrade
    e.toLinearMap hφ
  let g := associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade sourceGrade
    e.symm.toLinearMap hsymm
  have hfg : f ≫ g = 𝟙 _ := by
    have hc := associatedModuleSheafMap_comp
      (𝒮 := veroneseGrading 𝒮 d) (𝒨 := sourceGrade) (𝒩 := targetGrade) (𝒬 := sourceGrade)
      e.toLinearMap hφ e.symm.toLinearMap hsymm
    have heq : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext
      simp
    calc
      f ≫ g = associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade sourceGrade
          (e.symm.toLinearMap.comp e.toLinearMap) _ := hc.symm
      _ = associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade sourceGrade
          (LinearMap.id) _ := by congr 1
      _ = 𝟙 _ := associatedModuleSheafMap_id
        (𝒮 := veroneseGrading 𝒮 d) (𝒨 := sourceGrade)
  have hgf : g ≫ f = 𝟙 _ := by
    have hc := associatedModuleSheafMap_comp
      (𝒮 := veroneseGrading 𝒮 d) (𝒨 := targetGrade) (𝒩 := sourceGrade) (𝒬 := targetGrade)
      e.symm.toLinearMap hsymm e.toLinearMap hφ
    have heq : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext
      simp
    calc
      g ≫ f = associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade targetGrade
          (e.toLinearMap.comp e.symm.toLinearMap) _ := hc.symm
      _ = associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade targetGrade
          (LinearMap.id) _ := by congr 1
      _ = 𝟙 _ := associatedModuleSheafMap_id
        (𝒮 := veroneseGrading 𝒮 d) (𝒨 := targetGrade)
  exact ⟨f, g, hfg, hgf⟩

/-- `veroneseShiftedSheafIso` is the associated-sheaf map of `veroneseModuleShiftEquiv`. -/
public theorem veroneseShiftedSheafIso_hom (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 (shiftedGrading 𝒨 (n * d)) d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom =
      associatedModuleSheafMap (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d)
        (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)
        (veroneseModuleShiftEquiv 𝒮 𝒨 d n).toLinearMap
        (veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n) :=
  rfl

end AnyUniverse

variable {S M : Type u} {σ : Type w} [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]

/-- **Assertion (1) of Tag 0B5J at the shift `M(nd)`**: the canonical isomorphism
`M(nd)~ ≅ i^*(M(nd)'~)` followed by the identification `M(nd)' = M'(n)`. -/
public noncomputable def veroneseShiftedModuleIso (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 (shiftedGrading 𝒨 (n * d)) ≅
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  exact (associatedModuleSheafVeroneseIso 𝒮 (shiftedGrading 𝒨 (n * d)) d hd).trans
    ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).mapIso
      (veroneseShiftedSheafIso 𝒮 𝒨 d hd n))

/-- **`veroneseShiftedModuleIso` on a chart, on a homogeneous fraction.** It carries the section
`m / f^(pd)` of `M(nd)~` over `D₊(f)` to the pullback of the section `m / (f ᵈ)^p` of
`M'(n)~` over `D₊(f ᵈ)`. -/
public theorem veroneseShiftedModuleIso_hom_degreeZeroFraction (d : ℕ) (hd : 0 < d) (n : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p : ℕ)
    (mb : veroneseSubmodule 𝒮 (shiftedGrading 𝒨 (n * d)) d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d (p • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app (op (Proj.basicOpen 𝒮 f)))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
          (shiftedGrading 𝒨 (n * d)) hf he).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (shiftedGrading 𝒨 (n * d)) hf
            (p * d) (mb : M)
            (mem_of_mem_veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d p e hmb))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf p
              (veroneseModuleShiftEquiv 𝒮 𝒨 d n mb)
              (veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n (p • (e : ℤ)) mb hmb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  let := veroneseModuleGradingDecomposition 𝒮 (shiftedGrading 𝒨 (n * d)) d hd
  intro hvf
  have h1 := associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮
    (shiftedGrading 𝒨 (n * d)) d hd f he hf p mb hmb hvf
  have h2 := modulesPullbackUnit_naturality (veroneseProjIso 𝒮 d hd).hom
    (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d) hvf he).symm
      (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d) hvf p mb hmb))
  have h3 := associatedModuleSheafMap_degreeZeroFraction (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d)
    (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)
    (veroneseModuleShiftEquiv 𝒮 𝒨 d n).toLinearMap
    (veroneseModuleShiftEquiv_mem 𝒮 𝒨 d n) hvf he p mb hmb
  refine (congrArg (fun t => (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom).val.app (op (Proj.basicOpen 𝒮 f))) t) h1).trans ?_
  refine (moduleSheafHom_app_cast ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (veroneseShiftedSheafIso 𝒮 𝒨 d hd n).hom) (veroneseProjIso_basicOpen 𝒮 d hd f he hf)
      _).trans ?_
  refine congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸ t) (h2.trans ?_)
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))) h3

/-! ### The square -/

/-- The upper path of the square: the canonical map `M̃ ⊗ 𝒪_X(nd) ⟶ M(nd)~`, then
`veroneseShiftedModuleIso`. -/
public def veroneseModuleTwistLeft (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj ((twistingSheaf 𝒮 (n * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  exact Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap 𝒮 𝒨 (n * d) ≫
    (veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom

/-- The lower path of the square: assertion (1) on `M̃` and assertion (2) on `𝒪_X(nd)`, Tag 01CD
backwards, then the pullback of the canonical map `M'~ ⊗ 𝒪_{X'}(n) ⟶ M'(n)~`. -/
public def veroneseModuleTwistRight (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj ((twistingSheaf 𝒮 (n * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  exact ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
        (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩)).map
      (X := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨, twistingSheaf 𝒮 (n * d)))
      (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (veroneseModuleGrading 𝒮 𝒨 d)),
        (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (twistingSheaf (veroneseGrading 𝒮 d) n)))
      ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom,
        (veroneseTwistingSheafIso 𝒮 d hd n).hom)) ≫
    (veronesePullbackTensorIso 𝒮 d hd
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d))
      (twistingSheaf (veroneseGrading 𝒮 d) n)).inv ≫
    (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 𝒨 d) n)

/-- The upper path applied to a section. -/
public theorem veroneseModuleTwistLeft_app (d : ℕ) (hd : 0 < d) (n : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
          ((twistingSheaf 𝒮 (n * d))))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ((veroneseModuleTwistLeft 𝒮 𝒨 d hd n).val.app U).hom z =
      ((veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app U).hom
        (((Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap 𝒮 𝒨 (n * d)).val.app U).hom z) :=
  rfl

/-- The lower path applied to a section. -/
public theorem veroneseModuleTwistRight_app (d : ℕ) (hd : 0 < d) (n : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
          (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
        ((ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨))).obj
          ((twistingSheaf 𝒮 (n * d))))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ((veroneseModuleTwistRight 𝒮 𝒨 d hd n).val.app U).hom z =
      (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) n)).val.app U).hom
        (((veronesePullbackTensorIso 𝒮 d hd
              (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d))
              (twistingSheaf (veroneseGrading 𝒮 d) n)).inv.val.app U).hom
          (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
                (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩)).map
              (X := (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨, twistingSheaf 𝒮 (n * d)))
              (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
                  (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                    (veroneseModuleGrading 𝒮 𝒨 d)),
                (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
                  (twistingSheaf (veroneseGrading 𝒮 d) n)))
              ((associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom,
                (veroneseTwistingSheafIso 𝒮 d hd n).hom))).val.app U).hom z)) :=
  rfl

/-- The numerator of the canonical product of a Veronese-homogeneous fraction of `M'` with one
of `𝒪_{X'}(n)`, as an element of the shift `M'(n)`. -/
public theorem veroneseModuleTwist_numerator_mem (d : ℕ) (hd : 0 < d) (n : ℤ) {e : ℕ} (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (q • (e : ℤ))) :
    (TensorProduct.rid (veroneseSubring 𝒮 d) (veroneseSubmodule 𝒮 𝒨 d)).toLinearMap
        (mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd n nb) ∈
      shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n ((p + q) • (e : ℤ)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  exact Stacks.GradedModule.rid_mem_shiftedGrading (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) n _ _
    (Stacks.GradedModule.tmul_mem_tensorGrading _ _ (add_nsmul (e : ℤ) p q).symm hmb
      (veroneseShiftLinearEquiv_mem 𝒮 d hd n _ nb hnb))

/-- **The upper path on a chart**: `m / f^(pd)` and `a / f^(qd)` go to the pullback of
`am / (f ᵈ)^(p+q)`. -/
public theorem veroneseModuleTwistLeft_standardOpen (d : ℕ) (hd : 0 < d) (n : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseModuleTwistLeft 𝒮 𝒨 d hd n).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 (n * d))
          (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (n * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (n * d))
                hf (q * d) (nb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d q e
                  hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf (p + q)
              ((TensorProduct.rid (veroneseSubring 𝒮 d) (veroneseSubmodule 𝒮 𝒨 d)).toLinearMap
                (mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd n nb))
              (veroneseModuleTwist_numerator_mem 𝒮 𝒨 d hd n p q mb hmb nb hnb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  intro hvf
  let z := (TensorProduct.rid (veroneseSubring 𝒮 d) (veroneseSubmodule 𝒮 𝒨 d)).toLinearMap
    (mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd n nb)
  let w := (veroneseModuleShiftEquiv 𝒮 𝒨 d n).symm z
  have hw : w ∈ veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d ((p + q) • (e : ℤ)) :=
    veroneseModuleShiftEquiv_symm_mem 𝒮 𝒨 d n _ z
      (veroneseModuleTwist_numerator_mem 𝒮 𝒨 d hd n p q mb hmb nb hnb)
  have hwM : (w : M) = (TensorProduct.rid S M).toLinearMap ((mb : M) ⊗ₜ[S] (nb : S)) := by
    simp [w, z, veroneseModule_smul_def]
  have hpq : p * d + q * d = (p + q) * d := by ring
  have hwmem := mem_of_mem_veroneseModuleGrading 𝒮 (shiftedGrading 𝒨 (n * d)) d (p + q) e hw
  have hxm : (TensorProduct.rid S M).toLinearMap ((mb : M) ⊗ₜ[S] (nb : S)) ∈
      shiftedGrading 𝒨 (n * d) ((p * d + q * d) • (e : ℤ)) := by
    rw [← hwM, hpq]
    exact hwmem
  refine (veroneseModuleTwistLeft_app 𝒮 𝒨 d hd n _ _).trans ?_
  refine Eq.trans (congrArg (fun t => ((veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app
      (op (Proj.basicOpen 𝒮 f))).hom t)
    (moduleTwistMap_degreeZeroFraction 𝒮 𝒨 (n * d) hf he (p * d) (q * d) (mb : M) (nb : S)
      (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)
      (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d q e hnb)
      hxm)) ?_
  refine Eq.trans (congrArg (fun t => ((veroneseShiftedModuleIso 𝒮 𝒨 d hd n).hom.val.app
        (op (Proj.basicOpen 𝒮 f))).hom
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
        (shiftedGrading 𝒨 (n * d)) hf he).symm t))
    (degreeZeroFraction_congr 𝒮 (shiftedGrading 𝒨 (n * d)) hf hpq hwM.symm _ hwmem)) ?_
  refine (veroneseShiftedModuleIso_hom_degreeZeroFraction 𝒮 𝒨 d hd n f he hf (p + q) w hw
    hvf).trans ?_
  exact congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
      (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf he).symm t))
    (degreeZeroFraction_congr (veroneseGrading 𝒮 d)
      (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf rfl
      ((veroneseModuleShiftEquiv 𝒮 𝒨 d n).apply_symm_apply z) _ _)

/-- **The lower path on a chart**: also `m / f^(pd)` and `a / f^(qd)` go to the pullback of
`am / (f ᵈ)^(p+q)`. -/
public theorem veroneseModuleTwistRight_standardOpen (d : ℕ) (hd : 0 < d) (n : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 𝒨 d) (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseModuleTwistRight 𝒮 𝒨 d hd n).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 (n * d))
          (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
                (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (n * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (n * d))
                hf (q * d) (nb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d q e
                  hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
            (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n) hvf (p + q)
              ((TensorProduct.rid (veroneseSubring 𝒮 d) (veroneseSubmodule 𝒮 𝒨 d)).toLinearMap
                (mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd n nb))
              (veroneseModuleTwist_numerator_mem 𝒮 𝒨 d hd n p q mb hmb nb hnb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  intro hvf
  refine (veroneseModuleTwistRight_app 𝒮 𝒨 d hd n _ _).trans ?_
  refine Eq.trans (congrArg (fun t => (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (veroneseGrading 𝒮 d)
              (veroneseModuleGrading 𝒮 𝒨 d) n)).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (((veronesePullbackTensorIso 𝒮 d hd
              (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
                (veroneseModuleGrading 𝒮 𝒨 d))
              (twistingSheaf (veroneseGrading 𝒮 d) n)).inv.val.app
              (op (Proj.basicOpen 𝒮 f))).hom t))
    (tensorSheafMap_app_toTensorSheafSection_cast (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
      _ _ _ _ (associatedModuleSheafVeroneseIso 𝒮 𝒨 d hd).hom
      (veroneseTwistingSheafIso 𝒮 d hd n).hom
      (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _ _ _
      (associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮 𝒨 d hd f he hf p mb hmb hvf)
      (veroneseTwistingSheafIso_hom_degreeZeroFraction 𝒮 d hd n f he hf q nb hnb hvf))) ?_
  refine (pullbackMap_schemePullbackTensorIso_inv_cast (veroneseProjIso 𝒮 d hd).hom
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d))
    (twistingSheaf (veroneseGrading 𝒮 d) n)
    (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
      (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
    (Stacks.AlgebraicGeometry.ProjShifted.moduleTwistMap (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 𝒨 d) n)
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _).trans ?_
  exact congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (ProjectiveSpectrum.Proj.associatedModuleSheaf (veroneseGrading 𝒮 d)
        (shiftedGrading (veroneseModuleGrading 𝒮 𝒨 d) n))
      (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)) t)
    (moduleTwistMap_degreeZeroFraction (veroneseGrading 𝒮 d) (veroneseModuleGrading 𝒮 𝒨 d) n
      hvf he p q mb _ hmb (veroneseShiftLinearEquiv_mem 𝒮 d hd n _ nb hnb)
      (veroneseModuleTwist_numerator_mem 𝒮 𝒨 d hd n p q mb hmb nb hnb))

/-- **The square commutes on a chart**, for arbitrary sections. -/
public theorem veroneseModuleTwistCompatibility_chart (d : ℕ) (hd : 0 < d) (n : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e)
    (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (Proj.basicOpen 𝒮 f)))
    (y : (twistingSheaf 𝒮 (n * d)).val.obj (op (Proj.basicOpen 𝒮 f))) :
    ((veroneseModuleTwistLeft 𝒮 𝒨 d hd n).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 (n * d))
          (op (Proj.basicOpen 𝒮 f)) (x ⊗ₜ y)) =
      ((veroneseModuleTwistRight 𝒮 𝒨 d hd n).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨) (twistingSheaf 𝒮 (n * d))
          (op (Proj.basicOpen 𝒮 f)) (x ⊗ₜ y)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  obtain ⟨p, mb, hmb, rfl⟩ := exists_veroneseDegreeZeroFraction 𝒮 𝒨 d hd f he hf x
  obtain ⟨q, nb, hnb, rfl⟩ := exists_veroneseDegreeZeroFraction 𝒮
    (twistGradingAddSubgroup 𝒮 (n * d)) d hd f he hf y
  exact (veroneseModuleTwistLeft_standardOpen 𝒮 𝒨 d hd n f he hf p q mb hmb nb hnb hvf).trans
    (veroneseModuleTwistRight_standardOpen 𝒮 𝒨 d hd n f he hf p q mb hmb nb hnb hvf).symm

/-- **Tag 0B5J's isomorphisms are compatible with the canonical maps `M̃ ⊗ 𝒪(a) ⟶ M(a)~`.** For
every graded `S`-module `M` and integer `n` the square

`M̃ ⊗ 𝒪_X(nd) ⟶ M(nd)~ ⟶ i^*(M'(n)~)`
`= M̃ ⊗ 𝒪_X(nd) ⟶ i^*(M'~) ⊗ i^*𝒪_{X'}(n) ⟶ i^*(M'~ ⊗ 𝒪_{X'}(n)) ⟶ i^*(M'(n)~)`

commutes, where the horizontal maps are the canonical maps, the vertical ones assertion (1) for
`M` and for `M(nd)` (followed by `M(nd)' = M'(n)`) and assertion (2), and the crossing is
Tag 01CD. -/
public theorem veroneseModuleTwistCompatibility (d : ℕ) (hd : 0 < d) (n : ℤ) :
    veroneseModuleTwistLeft 𝒮 𝒨 d hd n = veroneseModuleTwistRight 𝒮 𝒨 d hd n := by
  let ι := { a : S × ℕ // 0 < a.2 ∧ a.1 ∈ 𝒮 a.2 }
  let W : ι → Opens (ProjectiveSpectrum.top 𝒮) :=
    fun a => ProjectiveSpectrum.basicOpen 𝒮 a.1.1
  have heq : Set.range W = positiveBasicOpenSet (𝒮 := 𝒮) := by
    ext V
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1.1, a.1.2, a.2.1, a.2.2, rfl⟩
    · rintro ⟨g, k, hk, hg, rfl⟩
      exact ⟨⟨(g, k), hk, hg⟩, rfl⟩
  have hW : Opens.IsBasis (Set.range W) := heq ▸ positiveBasicOpenSet_isBasis 𝒮
  exact tensorSheaf_hom_ext_onBasis_tmul (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
    _ _ _ _ _ W hW
    (fun a x y => veroneseModuleTwistCompatibility_chart 𝒮 𝒨 d hd n a.1.1 a.2.1 a.2.2 x y)

end Stacks.Veronese

end
