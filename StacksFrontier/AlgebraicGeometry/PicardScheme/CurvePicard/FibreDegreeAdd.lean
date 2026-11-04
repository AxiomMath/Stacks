module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponents
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.SectionDivisor
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapComponent

/-!
# The fibre degree of points of the Picard functor of a curve is additive

On a proper curve `Z` over a field `K` the Euler characteristic `χ(Z, L)` of an invertible module
differs from `χ(Z, 𝒪_Z)` by the degree of `L`, which is additive on `Pic(Z)` ([Stacks, Tag 0AYX]).
Applied to the fibres `X_t` of `X_T ⟶ T`, which are base changes of a smooth projective curve
to the residue fields of `T`, this makes the fibre degree
`deg(L_t) = χ(X_t, L_t) - χ(X_t, 𝒪)` of a point of the Picard functor additive.

## Main results

* `Stacks.PicardCurve.classEuler_add`: `χ(y₁ + y₂) + χ(0) = χ(y₁) + χ(y₂)` on a proper curve.
* `Stacks.PicardFunctor.fibreDegree_add`: the fibre degree is additive.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.SmallEtale (zariskiStructureIsSheaf)

universe u

namespace Stacks.PicardCurve

variable {K : Type u} [Field K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))

/-- **The Euler characteristic of a Picard class** of a scheme over a field,
`dim H⁰(Z, L) - dim H¹(Z, L)` for the chosen representative `L` of the class. -/
def classEuler (y : Stacks.Picard.ofScheme Z) : ℤ :=
  (Module.finrank K (cohomologyOverField K fZ (rep y) 0) : ℤ) -
    Module.finrank K (cohomologyOverField K fZ (rep y) 1)

variable [IsProper fZ] [IsCurve K fZ] (hdim : topologicalKrullDim Z ≤ 1)

include hdim in
/-- **On a proper scheme of dimension at most one over a field, the Euler characteristic of a
Picard class exceeds that of the structure sheaf by its degree.** -/
theorem classEuler_sub_eq_picardDegree (y : Stacks.Picard.ofScheme Z) :
    classEuler fZ y - ((Module.finrank K (cohomologyOverField K fZ
        (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ) -
      Module.finrank K (cohomologyOverField K fZ (SheafOfModules.unit Z.ringCatSheaf) 1)) =
      picardDegree K fZ hdim (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace y) := by
  have hS : Stacks.SheafOfModules.IsInvertible Z.presheaf (zariskiStructureIsSheaf Z) (rep y) :=
    (Stacks.Picard.picardRepresentative Z.toRingedSpace y).property
  have hy : Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace y =
      schemePicardClassOf Z (rep y) hS :=
    (congrArg (Stacks.GluePicard.picardModelAddEquiv Z.toRingedSpace)
      (Stacks.Picard.classOf_picardRepresentative Z.toRingedSpace y)).symm.trans
      (Stacks.GluePicard.picardModelAddEquiv_classOf _ _ hS)
  rw [hy, picardDegree_classOf]
  let := isInvertible_of_stacks_isInvertible Z (rep y) hS
  rw [invertibleCurveDegree_eq_sub_of_isZero K fZ hdim (rep y)
    (fun m hm => isZero_cohomologyOverField_of_two_le' K fZ hdim _ m hm)
    (fun m hm => isZero_cohomologyOverField_of_two_le' K fZ hdim _ m hm)]
  rfl

include hdim in
/-- **The Euler characteristic of Picard classes on a proper curve is affine-additive**:
`χ(y₁ + y₂) + χ(0) = χ(y₁) + χ(y₂)` (the degree is additive, [Stacks, Tag 0AYX]). -/
theorem classEuler_add (y₁ y₂ : Stacks.Picard.ofScheme Z) :
    classEuler fZ (y₁ + y₂) + classEuler fZ 0 = classEuler fZ y₁ + classEuler fZ y₂ := by
  have h := fun y => classEuler_sub_eq_picardDegree fZ hdim y
  have h12 := h (y₁ + y₂)
  have h0 := h 0
  rw [map_add, map_add] at h12
  rw [map_zero, map_zero] at h0
  have h1 := h y₁
  have h2 := h y₂
  omega

end Stacks.PicardCurve

namespace Stacks.PicardFunctor

open Stacks.PicardCurve Stacks.FibreCohomology

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 (Spec (.of k)))
  (hOiso : ∀ U : BigFppfOver B (Spec (.of k)) hk,
    IsIso (baseChangeProj B hX hk f U).toLRSHom.toHom.c)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]

omit [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
/-- The fibre Euler characteristic of the image of a class is the Euler characteristic of its
pullback to the fibre. -/
theorem fibreEuler_toPicardFunctorHom (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreEuler B hX hk f σ hσ hOiso T (toPicardFunctorHom B hX hk f T x) t =
      classEuler (fibreAtProj (baseChangeProj B hX hk f T) t)
        (Stacks.Picard.schemePullbackClass (fibreAtMap (baseChangeProj B hX hk f T) t) x) := by
  rw [fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom,
    classFibreRank_eq_fibre, classFibreRank_eq_fibre]
  rfl

/-- The fibre of `X_T ⟶ T` over a point is a proper curve over the residue field. -/
theorem isCurve_fibreAtProj (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    IsProper (fibreAtProj (baseChangeProj B hX hk f T) t) ∧
      IsCurve (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
        (fibreAtProj (baseChangeProj B hX hk f T) t) := by
  let : Algebra k ((B.inclusion.obj T.left).residueField t) :=
    residueAlgebra (B.inclusion.map T.hom) t
  let : Algebra k (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t) :=
    residueAlgebra (B.inclusion.map T.hom) t
  have hZ := isPullback_fiber (B.inclusion.map f) (B.inclusion.map T.hom)
    (pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)) (baseChangeProj B hX hk f T)
    (IsPullback.of_hasPullback _ _) t
  have hP : IsProper (fibreAtProj (baseChangeProj B hX hk f T) t) :=
    Stacks.AbelMap.isProper_of_isPullback (K := (B.inclusion.obj T.left).residueField t)
      _ _ _ hZ
  have hI := Stacks.AbelMap.isIntegral_of_isPullback (K := (B.inclusion.obj T.left).residueField t)
      _ _ _ hZ
  have hd := Stacks.AbelMap.topologicalKrullDim_eq_one_of_isPullback
      (K := (B.inclusion.obj T.left).residueField t)
      _ _ _ hZ
  exact ⟨hP, { toIsIntegral := hI, topologicalKrullDim_eq_one := hd }⟩

/-- **The fibre degree of points of the Picard functor of a curve is additive.** -/
theorem fibreDegree_add (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ η : (picardFunctor B hX hk f).obj (op T))
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreDegree B hX hk f σ hσ hOiso T (ξ + η) t =
      fibreDegree B hX hk f σ hσ hOiso T ξ t + fibreDegree B hX hk f σ hσ hOiso T η t := by
  obtain ⟨x, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T ξ
  obtain ⟨y, rfl⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ hOiso T η
  obtain ⟨hP, hC⟩ := isCurve_fibreAtProj B hX hk f T t
  have := hP
  have := hC
  have hdim : topologicalKrullDim (fibreAt (baseChangeProj B hX hk f T) t) ≤ 1 :=
    hC.topologicalKrullDim_eq_one.le
  have h := @classEuler_add _ _ _ (fibreAtProj (baseChangeProj B hX hk f T) t) hP hC hdim
    (Stacks.Picard.schemePullbackClass (fibreAtMap (baseChangeProj B hX hk f T) t) x)
    (Stacks.Picard.schemePullbackClass (fibreAtMap (baseChangeProj B hX hk f T) t) y)
  have hpb0 : Stacks.Picard.schemePullbackClass (fibreAtMap (baseChangeProj B hX hk f T) t)
      (0 : picardAt B hX hk f T) = 0 :=
    map_zero (Stacks.Picard.schemePullbackClassHom _)
  simp only [fibreDegree]
  rw [← map_add, ← (toPicardFunctorHom B hX hk f T).map_zero, fibreEuler_toPicardFunctorHom,
    fibreEuler_toPicardFunctorHom, fibreEuler_toPicardFunctorHom, fibreEuler_toPicardFunctorHom,
    Stacks.Picard.schemePullbackClass_add, hpb0]
  omega

/-- The pullback of the zero class is zero. -/
theorem schemePullbackClass_zero {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    Stacks.Picard.schemePullbackClass g (0 : Stacks.Picard.ofScheme Y) = 0 :=
  map_zero (Stacks.Picard.schemePullbackClassHom g)

/-- **The fibre Euler characteristic of the zero point is `1 - g`**: on each fibre `X_t`, a
geometrically integral proper curve of genus `g` over `κ(t)` ([Stacks, Tag 0BY9]),
`χ(X_t, 𝒪) = 1 - g`. -/
theorem fibreEuler_zero (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    fibreEuler B hX hk f σ hσ hOiso T 0 t = 1 - genus (B.inclusion.map f) := by
  obtain ⟨hP, hC⟩ := isCurve_fibreAtProj B hX hk f T t
  have hdim : topologicalKrullDim (fibreAt (baseChangeProj B hX hk f T) t) ≤ 1 :=
    hC.topologicalKrullDim_eq_one.le
  let : Algebra k ((B.inclusion.obj T.left).residueField t) :=
    residueAlgebra (B.inclusion.map T.hom) t
  have hZ := isPullback_fiber (B.inclusion.map f) (B.inclusion.map T.hom)
    (pullback.fst (B.inclusion.map f) (B.inclusion.map T.hom)) (baseChangeProj B hX hk f T)
    (IsPullback.of_hasPullback _ _) t
  have hiso := Stacks.AbelMap.isIso_globalSections_of_isPullback
    (K := (B.inclusion.obj T.left).residueField t) _ _ _ hZ
  have h := @classEuler_sub_eq_picardDegree _ _ _ (fibreAtProj (baseChangeProj B hX hk f T) t)
    hP hC hdim 0
  rw [map_zero, map_zero] at h
  have h1 := @genus_eq_finrank_cohomologyOverField_unit_one' _ _ _
    (fibreAtProj (baseChangeProj B hX hk f T) t)
  have h2 : genus (fibreAtProj (baseChangeProj B hX hk f T) t) = genus (B.inclusion.map f) :=
    genus_baseChange k ((B.inclusion.obj T.left).residueField t) _ _ _ hZ
  have h0 := @finrank_cohomologyOverField_unit_zero_eq_one _ _ _
    (fibreAtProj (baseChangeProj B hX hk f T) t) hiso
  rw [← (toPicardFunctorHom B hX hk f T).map_zero, fibreEuler_toPicardFunctorHom,
    schemePullbackClass_zero]
  omega

/-- **The degree-`d` subfunctor is the degree-`d` component of the Picard functor** in the sense
of `Stacks.AbelMap.IsDegreeComponent`: a class lies in it exactly when its fibres have Euler
characteristic `d + 1 - g`. -/
theorem isDegreeComponent_degreeSubfunctor (d : ℤ) :
    Stacks.AbelMap.IsDegreeComponent B hX hk f d (degreeSubfunctor B hX hk f σ hσ hOiso d) := by
  intro T L hL
  show (∀ t, fibreDegree B hX hk f σ hσ hOiso T _ t = d) ↔ _
  refine forall_congr' fun t => ?_
  rw [fibreDegree, fibreEuler_zero]
  have he : fibreEuler B hX hk f σ hσ hOiso T ((toPicardFunctor B hX hk f).app (op T)
      (Stacks.SheafOfModules.picardClass _ _ L hL)) t =
      (Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 0) : ℤ) -
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 1) := by
    show fibreEuler B hX hk f σ hσ hOiso T (toPicardFunctorHom B hX hk f T
      (Stacks.SheafOfModules.picardClass _ _ L hL)) t = _
    rw [fibreEuler, fibreRank_toPicardFunctorHom, fibreRank_toPicardFunctorHom,
      classFibreRank_picardClass, classFibreRank_picardClass]
    rfl
  rw [he]
  omega

end Stacks.PicardFunctor

end
