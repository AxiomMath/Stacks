module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTensorCompatibility
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseTwist
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseShift

/-!
# The Veronese comparison and the multiplication of twists

Let `S` be a graded ring, `d ≥ 1`, `S' = S⁽ᵈ⁾`, and `i : X = Proj S ≅ X' = Proj S'` the Veronese
isomorphism, with the canonical isomorphisms `T_n : 𝒪_X(nd) ≅ i^*𝒪_{X'}(n)` of Tag 0B5J's
assertion (2). This file proves that `T` is compatible with the multiplication maps
`𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)` of the twisting sheaves: the square

```
𝒪_X(nd) ⊗ 𝒪_X(md) ───── mult ─────▸ 𝒪_X((n+m)d)
   │ T_n ⊗ T_m                          │ T_{n+m}
   ▾                                     ▾
i^*𝒪'(n) ⊗ i^*𝒪'(m) ── 01CD⁻¹ ──▸ i^*(𝒪'(n) ⊗ 𝒪'(m)) ── i^* mult ──▸ i^*𝒪'(n+m)
```

commutes. It is checked on pure tensors of sections over the standard opens `D₊(f)` of
positive-degree homogeneous elements, where both paths send `a / f^(pd)` and `b / f^(qd)` to the
pullback of `ab / (f ᵈ)^(p+q)`.

## Main definitions

* `Stacks.Veronese.veroneseTwistMulLeft` and `Stacks.Veronese.veroneseTwistMulRight`: the two
  sides of the square.

## Main results

* `Stacks.Veronese.veroneseTwistMulCompatibility`: the square commutes.
* `Stacks.Veronese.veroneseTwistingSheafIso_hom_degreeZeroFraction`: the isomorphism `T_n` on a
  homogeneous fraction over a standard open.
* `Stacks.Veronese.associatedModuleSheafMap_degreeZeroFraction`: the sheaf map induced by a
  graded linear map, on a homogeneous fraction over a standard open.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory DirectSum TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
open Stacks.GradedModule (tensorGrading)
open _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj (twistGrading twistingSheaf)
open scoped TensorProduct

namespace Stacks.Veronese

attribute [local instance_reducible] TopCat.Sheaf
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

universe u w

section Generic

variable {A P Q : Type u} {ς τ υ : Type*} [CommRing A] [AddCommGroup P] [Module A P]
  [AddCommGroup Q] [Module A Q] [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜]
  [SetLike τ P] [AddSubgroupClass τ P] (ℒ : ℤ → τ) [Decomposition ℒ] [SetLike.GradedSMul 𝒜 ℒ]
  [SetLike υ Q] [AddSubgroupClass υ Q] (𝒬 : ℤ → υ) [Decomposition 𝒬] [SetLike.GradedSMul 𝒜 𝒬]

/-- **The sheaf map of a graded linear map on a homogeneous fraction.** Over `D₊(f)` the map of
associated sheaves induced by `φ` sends the section `m / f ᵏ` to `φ(m) / f ᵏ`. -/
public theorem associatedModuleSheafMap_degreeZeroFraction (φ : P →ₗ[A] Q)
    (hφ : ∀ i (m : P), m ∈ ℒ i → φ m ∈ 𝒬 i) {f : A} {c : ℕ} (hf : f ∈ 𝒜 c) (hc : 0 < c)
    (k : ℕ) (m : P) (hm : m ∈ ℒ (k • (c : ℤ))) :
    (associatedModuleSheafMap 𝒜 ℒ 𝒬 φ hφ).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 f))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 ℒ hf hc).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 ℒ hf k m hm)) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 𝒬 hf hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 𝒬 hf k (φ m) (hφ _ m hm)) := by
  apply (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜 𝒬 hf hc).injective
  rw [LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [associatedModuleSheafMap_standardOpen, LinearEquiv.apply_symm_apply]
  exact LocalizedModule.map_mk _ _ _ _

end Generic

/-- **The multiplication of twists on a chart.** Over `D₊(g)` the map `𝒪(a) ⊗ 𝒪(b) ⟶ 𝒪(a + b)`
sends the pure tensor of `x / g ᵏ` and `y / g ˡ` to `xy / g^(k+l)`. -/
public theorem twistMultiplicationMap_degreeZeroFraction {A : Type u} {ς : Type*} [CommRing A]
    [SetLike ς A] [AddSubgroupClass ς A] (𝒜 : ℕ → ς) [GradedRing 𝒜] (a b : ℤ)
    {g : A} {c : ℕ} (hg : g ∈ 𝒜 c) (hc : 0 < c) (k l : ℕ) (x y : A)
    (hx : x ∈ twistGrading (S := A) 𝒜 a (k • (c : ℤ)))
    (hy : y ∈ twistGrading (S := A) 𝒜 b (l • (c : ℤ)))
    (hxy : (TensorProduct.lid A A).toLinearMap (x ⊗ₜ y) ∈
      twistGrading (S := A) 𝒜 (a + b) ((k + l) • (c : ℤ))) :
    ((Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒜 a b).val.app
        (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒜).toRingedSpace
          (twistingSheaf 𝒜 a) (twistingSheaf 𝒜 b) (op (ProjectiveSpectrum.basicOpen 𝒜 g))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
              (twistGrading (S := A) 𝒜 a) hg hc).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 a) hg k x
                hx) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
              (twistGrading (S := A) 𝒜 b) hg hc).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 b) hg l y
                hy))) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒜
          (twistGrading (S := A) 𝒜 (a + b)) hg hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒜 (twistGrading (S := A) 𝒜 (a + b)) hg
          (k + l) ((TensorProduct.lid A A).toLinearMap (x ⊗ₜ y)) hxy) := by
  let := tensorGrading_decomposition (S := A) 𝒜
    (twistGrading (S := A) 𝒜 a) (twistGrading (S := A) 𝒜 b)
  let := tensorGrading_gradedSMul (S := A) 𝒜
    (twistGrading (S := A) 𝒜 a) (twistGrading (S := A) 𝒜 b)
  change ((associatedModuleSheafMap 𝒜
      (tensorGrading (S := A) (twistGrading (S := A) 𝒜 a) (twistGrading (S := A) 𝒜 b))
      (twistGrading (S := A) 𝒜 (a + b)) (TensorProduct.lid A A).toLinearMap
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplication_preserves_grading
        𝒜 a b)).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom
      (((associatedModuleSheafTensorMap 𝒜 (twistGrading (S := A) 𝒜 a)
        (twistGrading (S := A) 𝒜 b)).val.app (op (ProjectiveSpectrum.basicOpen 𝒜 g))).hom _) = _
  rw [associatedModuleSheafTensorMap_standardOpen]
  exact associatedModuleSheafMap_degreeZeroFraction 𝒜 _ _ _ _ hg hc (k + l) _ _

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- Transport of a section of a twisting sheaf along an equality of twists, on a fraction. -/
public theorem eqToHom_twistingSheaf_degreeZeroFraction {a b : ℤ} (h : a = b) {f : S} {c : ℕ}
    (hf : f ∈ 𝒮 c) (hc : 0 < c) (k : ℕ) (x : S)
    (hx : x ∈ twistGrading (S := S) 𝒮 a (k • (c : ℤ)))
    (hx' : x ∈ twistGrading (S := S) 𝒮 b (k • (c : ℤ))) :
    (eqToHom (congrArg (ProjectiveSpectrum.Proj.twistingSheaf 𝒮) h)).val.app
        (op (ProjectiveSpectrum.basicOpen 𝒮 f))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
          (twistGrading (S := S) 𝒮 a) hf hc).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 a) hf k x hx)) =
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
          (twistGrading (S := S) 𝒮 b) hf hc).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 b) hf k x hx') := by
  subst h
  rfl

/-- **Assertion (2) of Tag 0B5J on a chart, on a homogeneous fraction.** The isomorphism
`T_n : 𝒪_X(nd) ≅ i^*𝒪_{X'}(n)` carries the section `a / f^(pd)` over `D₊(f)`, whose numerator is
Veronese-homogeneous of degree `p` in `S(nd)`, to the pullback of the section `a / (f ᵈ)^p` of
`𝒪_{X'}(n)` over `D₊(f ᵈ)`. -/
public theorem veroneseTwistingSheafIso_hom_degreeZeroFraction (d : ℕ) (hd : 0 < d) (n : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p : ℕ)
    (mb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (p • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseTwistingSheafIso 𝒮 d hd n).hom.val.app (op (Proj.basicOpen 𝒮 f)))
        ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
          (twistGrading (S := S) 𝒮 (n * d)) hf he).symm
          (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (n * d)) hf
            (p * d) (mb : S)
            (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d p e
              hmb))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (twistingSheaf (veroneseGrading 𝒮 d) n)
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n) hvf he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n) hvf p
              (veroneseShiftLinearEquiv 𝒮 d hd n mb)
              (veroneseShiftLinearEquiv_mem 𝒮 d hd n (p • (e : ℤ)) mb hmb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d hd
  intro hvf
  have h1 := associatedModuleSheafVeroneseIso_hom_degreeZeroFraction 𝒮
    (twistGradingAddSubgroup 𝒮 (n * d)) d hd f he hf p mb hmb hvf
  have h2 := modulesPullbackUnit_naturality (veroneseProjIso 𝒮 d hd).hom
    (veroneseShiftSheafIso 𝒮 d hd n).hom
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
      (veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d) hvf he).symm
      (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d) hvf p mb hmb))
  have h3 := associatedModuleSheafMap_degreeZeroFraction (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n)
    (veroneseShiftLinearEquiv 𝒮 d hd n).toLinearMap
    (veroneseShiftLinearEquiv_mem 𝒮 d hd n) hvf he p mb hmb
  refine (congrArg (fun t => (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (veroneseShiftSheafIso 𝒮 d hd n).hom).val.app (op (Proj.basicOpen 𝒮 f))) t) h1).trans ?_
  refine (moduleSheafHom_app_cast ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (veroneseShiftSheafIso 𝒮 d hd n).hom) (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _).trans ?_
  refine congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸ t) (h2.trans ?_)
  exact congrArg (Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
    (twistingSheaf (veroneseGrading 𝒮 d) n)
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))) h3

/-! ### The square -/

/-- The upper path of the square: multiply on `Proj S`, identify `𝒪((nd) + (md))` with
`𝒪((n + m)d)`, and transport by `T_{n+m}`. -/
public def veroneseTwistMulLeft (d : ℕ) (hd : 0 < d) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
            (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
          ((twistingSheaf 𝒮 (n * d)))).obj ((twistingSheaf 𝒮 (m * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (twistingSheaf (veroneseGrading 𝒮 d) (n + m)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap 𝒮 (n * d) (m * d) ≫
    eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm) ≫
    (veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom

/-- The lower path of the square: transport both factors by `T`, cross Tag 01CD, and pull back
the multiplication of `Proj S⁽ᵈ⁾`. -/
public def veroneseTwistMulRight (d : ℕ) (hd : 0 < d) (n m : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
            (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
          ((twistingSheaf 𝒮 (n * d)))).obj ((twistingSheaf 𝒮 (m * d)))) ⟶
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (twistingSheaf (veroneseGrading 𝒮 d) (n + m)) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨(_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.presheaf,
        (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace.IsSheaf⟩)).map
      (X := (twistingSheaf 𝒮 (n * d), twistingSheaf 𝒮 (m * d)))
      (Y := ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (twistingSheaf (veroneseGrading 𝒮 d) n),
        (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
          (twistingSheaf (veroneseGrading 𝒮 d) m)))
      ((veroneseTwistingSheafIso 𝒮 d hd n).hom,
        (veroneseTwistingSheafIso 𝒮 d hd m).hom) ≫
    (veronesePullbackTensorIso 𝒮 d hd (twistingSheaf (veroneseGrading 𝒮 d) n)
      (twistingSheaf (veroneseGrading 𝒮 d) m)).inv ≫
    (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
      (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
        (veroneseGrading 𝒮 d) n m)

/-- The upper path of the square applied to a section. -/
public theorem veroneseTwistMulLeft_app (d : ℕ) (hd : 0 < d) (n m : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
            (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
          ((twistingSheaf 𝒮 (n * d)))).obj ((twistingSheaf 𝒮 (m * d))))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := tensorGrading_decomposition (S := S) 𝒮
      (twistGrading (S := S) 𝒮 (n * d)) (twistGrading (S := S) 𝒮 (m * d))
    letI := tensorGrading_gradedSMul (S := S) 𝒮
      (twistGrading (S := S) 𝒮 (n * d)) (twistGrading (S := S) 𝒮 (m * d))
    ((veroneseTwistMulLeft 𝒮 d hd n m).val.app U).hom z =
      ((veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom.val.app U).hom
        (((eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm)).val.app U).hom
          (((associatedModuleSheafMap 𝒮
              (tensorGrading (S := S) (twistGrading (S := S) 𝒮 (n * d))
                (twistGrading (S := S) 𝒮 (m * d)))
              (twistGrading (S := S) 𝒮 (n * d + m * d))
              (TensorProduct.lid S S).toLinearMap
              (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplication_preserves_grading
                𝒮 (n * d) (m * d))).val.app U).hom
            (((associatedModuleSheafTensorMap 𝒮 (twistGrading (S := S) 𝒮 (n * d))
              (twistGrading (S := S) 𝒮 (m * d))).val.app U).hom z))) :=
  rfl

/-- The lower path of the square applied to a section. -/
public theorem veroneseTwistMulRight_app (d : ℕ) (hd : 0 < d) (n m : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (z : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
            (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩).obj
          ((twistingSheaf 𝒮 (n * d)))).obj ((twistingSheaf 𝒮 (m * d))))).val.obj U) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ((veroneseTwistMulRight 𝒮 d hd n m).val.app U).hom z =
      (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
              (veroneseGrading 𝒮 d) n m)).val.app U).hom
        (((veronesePullbackTensorIso 𝒮 d hd (twistingSheaf (veroneseGrading 𝒮 d) n)
              (twistingSheaf (veroneseGrading 𝒮 d) m)).inv.val.app U).hom
          (((((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨(((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).presheaf,
                  (((_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace)).IsSheaf⟩)).map
                (((veroneseTwistingSheafIso 𝒮 d hd n).hom,
                  (veroneseTwistingSheafIso 𝒮 d hd m).hom) : (_, _) ⟶ (_, _)))).val.app U).hom
            z)) :=
  rfl

/-- The numerator of the product of two Veronese-homogeneous fractions, on `Proj S⁽ᵈ⁾`: the
product `ab` of the two numerators, read as an element of the twist `S⁽ᵈ⁾(n + m)`. -/
public theorem veroneseTwistMul_numerator_mem (d : ℕ) (hd : 0 < d) (n m : ℤ) {e : ℕ} (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d (q • (e : ℤ))) :
    (TensorProduct.lid (veroneseSubring 𝒮 d) (veroneseSubring 𝒮 d)).toLinearMap
        (veroneseShiftLinearEquiv 𝒮 d hd n mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd m nb) ∈
      twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)
        ((p + q) • (e : ℤ)) :=
  let := veroneseGradingGradedRing 𝒮 d hd
  Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplication_preserves_grading
    (veroneseGrading 𝒮 d) n m _ _
    (Stacks.GradedModule.tmul_mem_tensorGrading _ _ (add_nsmul (e : ℤ) p q).symm
      (veroneseShiftLinearEquiv_mem 𝒮 d hd n _ mb hmb)
      (veroneseShiftLinearEquiv_mem 𝒮 d hd m _ nb hnb))

/-- **The upper path of the square on a chart.** On `D₊(f)` it sends the pure tensor of
`a / f^(pd)` and `b / f^(qd)` to the pullback of the section `ab / (f ᵈ)^(p+q)` of
`𝒪_{X'}(n + m)`. -/
public theorem veroneseTwistMulLeft_standardOpen (d : ℕ) (hd : 0 < d) (n m : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseTwistMulLeft 𝒮 d hd n m).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 (n * d)) (twistingSheaf 𝒮 (m * d)) (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (n * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (n * d))
                hf (p * d) (mb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d p e
                  hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (m * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (m * d))
                hf (q * d) (nb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d q e
                  hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (twistingSheaf (veroneseGrading 𝒮 d) (n + m))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf
              he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf
              (p + q)
              ((TensorProduct.lid (veroneseSubring 𝒮 d) (veroneseSubring 𝒮 d)).toLinearMap
                (veroneseShiftLinearEquiv 𝒮 d hd n mb ⊗ₜ
                  veroneseShiftLinearEquiv 𝒮 d hd m nb))
              (veroneseTwistMul_numerator_mem 𝒮 d hd n m p q mb hmb nb hnb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := tensorGrading_decomposition (S := S) 𝒮
    (twistGrading (S := S) 𝒮 (n * d)) (twistGrading (S := S) 𝒮 (m * d))
  let := tensorGrading_gradedSMul (S := S) 𝒮
    (twistGrading (S := S) 𝒮 (n * d)) (twistGrading (S := S) 𝒮 (m * d))
  intro hvf
  let z := (TensorProduct.lid (veroneseSubring 𝒮 d) (veroneseSubring 𝒮 d)).toLinearMap
    (veroneseShiftLinearEquiv 𝒮 d hd n mb ⊗ₜ veroneseShiftLinearEquiv 𝒮 d hd m nb)
  let w := (veroneseShiftLinearEquiv 𝒮 d hd (n + m)).symm z
  have hw : w ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 ((n + m) * d)) d
      ((p + q) • (e : ℤ)) :=
    veroneseShiftLinearEquiv_symm_mem 𝒮 d hd (n + m) _ z
      (veroneseTwistMul_numerator_mem 𝒮 d hd n m p q mb hmb nb hnb)
  have hsh : veroneseShiftLinearEquiv 𝒮 d hd (n + m) w = z :=
    (veroneseShiftLinearEquiv 𝒮 d hd (n + m)).apply_symm_apply z
  have hwS : (w : S) = (TensorProduct.lid S S).toLinearMap ((mb : S) ⊗ₜ[S] (nb : S)) := by
    have h1 := congrArg Subtype.val hsh
    rw [coe_veroneseShiftLinearEquiv] at h1
    rw [h1]
    simp [z, smul_eq_mul]
  refine (veroneseTwistMulLeft_app 𝒮 d hd n m _ _).trans ?_
  refine Eq.trans (congrArg ((veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom.val.app
      (op (Proj.basicOpen 𝒮 f))).hom
    (Eq.trans (congrArg ((eqToHom (congrArg (twistingSheaf 𝒮) (add_mul n m (d : ℤ)).symm)).val.app
        (op (Proj.basicOpen 𝒮 f))).hom
      (Eq.trans (congrArg _
        (associatedModuleSheafTensorMap_standardOpen 𝒮 (twistGrading (S := S) 𝒮 (n * d))
          (twistGrading (S := S) 𝒮 (m * d)) hf he (p * d) (q * d) (mb : S)
          (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d p e hmb)
          (nb : S)
          (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d q e hnb)))
        (associatedModuleSheafMap_degreeZeroFraction 𝒮 _ _ _ _ hf he (p * d + q * d) _ _)))
      (eqToHom_twistingSheaf_degreeZeroFraction 𝒮 (add_mul n m (d : ℤ)).symm hf he
        (p * d + q * d) _ _
        (by
          rw [← hwS, show p * d + q * d = (p + q) * d by ring]
          exact mem_of_mem_veroneseModuleGrading 𝒮
            (twistGradingAddSubgroup 𝒮 ((n + m) * d)) d (p + q) e hw)))) ?_
  refine Eq.trans (congrArg ((veroneseTwistingSheafIso 𝒮 d hd (n + m)).hom.val.app
        (op (Proj.basicOpen 𝒮 f))).hom
    (congrArg (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
        (twistGrading (S := S) 𝒮 ((n + m) * d)) hf he).symm
      (degreeZeroFraction_congr 𝒮 (twistGrading (S := S) 𝒮 ((n + m) * d)) hf
        (show p * d + q * d = (p + q) * d by ring) hwS.symm _
        (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 ((n + m) * d)) d (p + q) e
          hw)))) ?_
  refine (veroneseTwistingSheafIso_hom_degreeZeroFraction 𝒮 d hd (n + m) f he hf (p + q) w hw
    hvf).trans ?_
  exact congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistingSheaf (veroneseGrading 𝒮 d) (n + m))
      (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
      ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
          (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf he).symm t))
    (degreeZeroFraction_congr (veroneseGrading 𝒮 d)
      (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf rfl hsh _ _)

/-- **The lower path of the square on a chart.** On `D₊(f)` it also sends the pure tensor of
`a / f^(pd)` and `b / f^(qd)` to the pullback of `ab / (f ᵈ)^(p+q)`. -/
public theorem veroneseTwistMulRight_standardOpen (d : ℕ) (hd : 0 < d) (n m : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e) (p q : ℕ)
    (mb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hmb : mb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d (p • (e : ℤ)))
    (nb : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d)
    (hnb : nb ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d (q • (e : ℤ))) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    ∀ hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e,
    ((veroneseTwistMulRight 𝒮 d hd n m).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 (n * d)) (twistingSheaf 𝒮 (m * d)) (op (Proj.basicOpen 𝒮 f))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (n * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (n * d))
                hf (p * d) (mb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d p e
                  hmb)) ⊗ₜ
            (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮
              (twistGrading (S := S) 𝒮 (m * d)) hf he).symm
              (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 (twistGrading (S := S) 𝒮 (m * d))
                hf (q * d) (nb : S)
                (mem_of_mem_veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (m * d)) d q e
                  hnb)))) =
      veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
        Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
          (twistingSheaf (veroneseGrading 𝒮 d) (n + m))
          (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
          ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf
              he).symm
            (ProjectiveSpectrum.Proj.degreeZeroFraction (veroneseGrading 𝒮 d)
              (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) (n + m)) hvf
              (p + q)
              ((TensorProduct.lid (veroneseSubring 𝒮 d) (veroneseSubring 𝒮 d)).toLinearMap
                (veroneseShiftLinearEquiv 𝒮 d hd n mb ⊗ₜ
                  veroneseShiftLinearEquiv 𝒮 d hd m nb))
              (veroneseTwistMul_numerator_mem 𝒮 d hd n m p q mb hmb nb hnb))) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  intro hvf
  refine (veroneseTwistMulRight_app 𝒮 d hd n m _ _).trans ?_
  refine Eq.trans (congrArg (fun t => (((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).map
            (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
              (veroneseGrading 𝒮 d) n m)).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (((veronesePullbackTensorIso 𝒮 d hd (twistingSheaf (veroneseGrading 𝒮 d) n)
              (twistingSheaf (veroneseGrading 𝒮 d) m)).inv.val.app
              (op (Proj.basicOpen 𝒮 f))).hom t))
    (tensorSheafMap_app_toTensorSheafSection_cast (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
      _ _ _ _ (veroneseTwistingSheafIso 𝒮 d hd n).hom (veroneseTwistingSheafIso 𝒮 d hd m).hom
      (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _ _ _
      (veroneseTwistingSheafIso_hom_degreeZeroFraction 𝒮 d hd n f he hf p mb hmb hvf)
      (veroneseTwistingSheafIso_hom_degreeZeroFraction 𝒮 d hd m f he hf q nb hnb hvf))) ?_
  refine (pullbackMap_schemePullbackTensorIso_inv_cast (veroneseProjIso 𝒮 d hd).hom
    (twistingSheaf (veroneseGrading 𝒮 d) n) (twistingSheaf (veroneseGrading 𝒮 d) m)
    (twistingSheaf (veroneseGrading 𝒮 d) (n + m))
    (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
      (veroneseGrading 𝒮 d) n m)
    (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf))
    (veroneseProjIso_basicOpen 𝒮 d hd f he hf) _ _).trans ?_
  exact congrArg (fun t => veroneseProjIso_basicOpen 𝒮 d hd f he hf ▸
    Stacks.Tag01VSPullbackTensor.modulesPullbackUnit (veroneseProjIso 𝒮 d hd).hom
      (twistingSheaf (veroneseGrading 𝒮 d) (n + m))
      (Proj.basicOpen (veroneseGrading 𝒮 d) (veronesePower 𝒮 d f hf)) t)
    (twistMultiplicationMap_degreeZeroFraction (veroneseGrading 𝒮 d) n m hvf he p q _ _
      (veroneseShiftLinearEquiv_mem 𝒮 d hd n _ mb hmb)
      (veroneseShiftLinearEquiv_mem 𝒮 d hd m _ nb hnb)
      (veroneseTwistMul_numerator_mem 𝒮 d hd n m p q mb hmb nb hnb))

/-- **Every section of `M̃` over a chart is a Veronese fraction.** Over `D₊(f)` every section of
the sheaf associated to a graded `S`-module `M` is `m / f^(pd)` for a numerator `m` which is
Veronese-homogeneous of degree `p`: write its image in `M₍f₎` as the image of a degree-zero
fraction of `M'₍f ᵈ₎` under the Veronese identification. -/
public theorem exists_veroneseDegreeZeroFraction {M : Type u} [AddCommGroup M] [Module S M]
    (𝒨 : ℤ → AddSubgroup M) [Decomposition 𝒨] [SetLike.GradedSMul 𝒮 𝒨]
    (d : ℕ) (hd : 0 < d) (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e)
    (x : (ProjectiveSpectrum.Proj.associatedModuleSheaf 𝒮 𝒨).val.obj
      (op (ProjectiveSpectrum.basicOpen 𝒮 f))) :
    ∃ (p : ℕ) (mb : veroneseSubmodule 𝒮 𝒨 d)
      (hmb : mb ∈ veroneseModuleGrading 𝒮 𝒨 d (p • (e : ℤ))),
      x = (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
        (ProjectiveSpectrum.Proj.degreeZeroFraction 𝒮 𝒨 hf (p * d) (mb : M)
          (mem_of_mem_veroneseModuleGrading 𝒮 𝒨 d p e hmb)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  let := veroneseModuleGradingDecomposition 𝒮 𝒨 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  obtain ⟨p, mb, hmb, hzM⟩ := exists_degreeZeroFraction (veroneseGrading 𝒮 d)
    (veroneseModuleGrading 𝒮 𝒨 d) (veronesePower 𝒮 d f hf) hvf
    ((veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd).symm
      (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he x))
  exact ⟨p, mb, hmb, ((ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv
        𝒮 𝒨 hf he).symm_apply_apply x).symm.trans
      (congrArg (ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv 𝒮 𝒨 hf he).symm
        ((((veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd).apply_symm_apply _).symm.trans
            (congrArg (veroneseModuleAwayEquiv 𝒮 d 𝒨 f hf hd) hzM)).trans
          (veroneseModuleAwayEquiv_degreeZeroFraction 𝒮 𝒨 d hd f hf p mb hmb hvf)))⟩

/-- **The square of the multiplication of twists commutes on a chart**, for arbitrary sections. -/
public theorem veroneseTwistMulCompatibility_chart (d : ℕ) (hd : 0 < d) (n m : ℤ)
    (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e)
    (x : (twistingSheaf 𝒮 (n * d)).val.obj (op (Proj.basicOpen 𝒮 f)))
    (y : (twistingSheaf 𝒮 (m * d)).val.obj (op (Proj.basicOpen 𝒮 f))) :
    ((veroneseTwistMulLeft 𝒮 d hd n m).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 (n * d)) (twistingSheaf 𝒮 (m * d)) (op (Proj.basicOpen 𝒮 f))
          (x ⊗ₜ y)) =
      ((veroneseTwistMulRight 𝒮 d hd n m).val.app (op (Proj.basicOpen 𝒮 f))).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
          (_root_.AlgebraicGeometry.Proj 𝒮).toRingedSpace
          (twistingSheaf 𝒮 (n * d)) (twistingSheaf 𝒮 (m * d)) (op (Proj.basicOpen 𝒮 f))
          (x ⊗ₜ y)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  have hvf : veronesePower 𝒮 d f hf ∈ veroneseGrading 𝒮 d e := veronesePower_mem 𝒮 d f hf
  obtain ⟨p, mb, hmb, rfl⟩ := exists_veroneseDegreeZeroFraction 𝒮
    (twistGradingAddSubgroup 𝒮 (n * d)) d hd f he hf x
  obtain ⟨q, nb, hnb, rfl⟩ := exists_veroneseDegreeZeroFraction 𝒮
    (twistGradingAddSubgroup 𝒮 (m * d)) d hd f he hf y
  exact (veroneseTwistMulLeft_standardOpen 𝒮 d hd n m f he hf p q mb hmb nb hnb hvf).trans
    (veroneseTwistMulRight_standardOpen 𝒮 d hd n m f he hf p q mb hmb nb hnb hvf).symm

/-- **Tag 0B5J's assertion (2) is compatible with the multiplication of twists.** For all
integers `n` and `m` the square

`𝒪_X(nd) ⊗ 𝒪_X(md) ⟶ 𝒪_X((n+m)d) ⟶ i^*𝒪_{X'}(n+m)`
`= 𝒪_X(nd) ⊗ 𝒪_X(md) ⟶ i^*𝒪_{X'}(n) ⊗ i^*𝒪_{X'}(m) ⟶ i^*(𝒪_{X'}(n) ⊗ 𝒪_{X'}(m)) ⟶ i^*𝒪_{X'}(n+m)`

commutes, where the horizontal maps are the multiplication maps of the twisting sheaves, the
vertical ones the isomorphisms `T` of assertion (2), and the crossing is Tag 01CD. -/
public theorem veroneseTwistMulCompatibility (d : ℕ) (hd : 0 < d) (n m : ℤ) :
    veroneseTwistMulLeft 𝒮 d hd n m = veroneseTwistMulRight 𝒮 d hd n m := by
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
    (fun a x y => veroneseTwistMulCompatibility_chart 𝒮 d hd n m a.1.1 a.2.1 a.2.2 x y)

end Stacks.Veronese

end
