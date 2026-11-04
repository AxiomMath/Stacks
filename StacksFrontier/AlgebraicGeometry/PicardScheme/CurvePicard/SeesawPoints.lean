/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.AbelJacobi
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponentProper
public import StacksFrontier.AlgebraicGeometry.Variety.RationalPointsHomExt

/-!
# The seesaw principle at rational points

Let `X` be a smooth projective curve over an algebraically closed field `k` with a rational point,
and let `T` be a reduced test scheme locally of finite type over `k`. A class `x ∈ Pic(X ×_k T)`
with degree-zero fibres whose restriction to `X ×_k {t}` is trivial for every rational point `t`
of `T` is pulled back from `T` (`Stacks.PicardFunctor.exists_eq_schemePullbackClass_of_points`):
its classifying map `T ⟶ J` sends every rational point to the origin, so it is the constant map
(`Stacks.Varieties.overHom_ext_of_points`), and the seesaw principle
`Stacks.PicardFunctor.classifyingMap_eq_classifyingMap_iff` applies.

This is the form of the seesaw principle used to identify classes on `C × C` in the proof of
[Stacks, Tag 03U1].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace Stacks.PicardFunctor

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  [(picardFunctor B hX hk f).IsRepresentable]

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The zero class of `Pic(X ×_k T)` has degree-zero fibres. -/
theorem hasDegreeZero_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    HasDegreeZero B hX hk f σ hσ T 0 := by
  rw [HasDegreeZero, map_zero]
  exact zero_mem _

/-- The classifying map of the zero class is the constant map to the origin. -/
theorem classifyingMap_zero (T : BigFppfOver B (Spec (.of k)) hk) :
    classifyingMap B hX hk f σ hσ T 0 (hasDegreeZero_zero B hX hk f σ hσ T) = 1 := by
  have h := classifyingMap_add B hX hk f σ hσ T (hasDegreeZero_zero B hX hk f σ hσ T)
    (hasDegreeZero_zero B hX hk f σ hσ T)
  have h' : classifyingMap B hX hk f σ hσ T (0 + 0) (hasDegreeZero_add B hX hk f σ hσ
      (hasDegreeZero_zero B hX hk f σ hσ T) (hasDegreeZero_zero B hX hk f σ hσ T)) =
      classifyingMap B hX hk f σ hσ T 0 (hasDegreeZero_zero B hX hk f σ hσ T) := by
    congr 1
    exact add_zero 0
  rw [h'] at h
  exact (mul_eq_left.1 h.symm)

variable [IsAlgClosed k]

include σ hσ in
/-- **The seesaw principle at rational points.** A class of `Pic(X ×_k T)` with degree-zero
fibres whose pullback along every rational point of `T` is trivial is pulled back from `T`. -/
theorem exists_eq_schemePullbackClass_of_points (T : BigFppfOver B (Spec (.of k)) hk)
    [IsReduced ((Over.post (X := B.obj hk) B.inclusion).obj T).left]
    [LocallyOfFiniteType ((Over.post (X := B.obj hk) B.inclusion).obj T).hom]
    (x : picardAt B hX hk f T) (hx : HasDegreeZero B hX hk f σ hσ T x)
    (h0 : ∀ g : baseObj B hk ⟶ T, picardMap B hX hk f g x = 0) :
    ∃ N : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T),
      Stacks.Picard.schemePullbackClass (baseChangeProj B hX hk f T) N = x := by
  have := isAbelianVariety_jacobian B hX hk f σ hσ
  have hcm : classifyingMap B hX hk f σ hσ T x hx =
      classifyingMap B hX hk f σ hσ T 0 (hasDegreeZero_zero B hX hk f σ hσ T) := by
    apply Stacks.Varieties.overHom_ext_of_points
    intro p
    have hp : p.left ≫ B.inclusion.map T.hom = 𝟙 _ := Over.w p
    set g := baseObjHomOfSection B hk T p.left hp
    have e1 := classifyingMap_comp B hX hk f σ hσ g x hx
    have e2 := classifyingMap_comp B hX hk f σ hσ g 0 (hasDegreeZero_zero B hX hk f σ hσ T)
    have e3 : picardMap B hX hk f g x = picardMap B hX hk f g 0 := by
      rw [h0 g]
      exact ((Stacks.Picard.schemePullbackClassHom (baseChangeMap B hX hk f g)).map_zero).symm
    have key : (Over.post (X := B.obj hk) B.inclusion).map g ≫
        classifyingMap B hX hk f σ hσ T x hx =
        (Over.post (X := B.obj hk) B.inclusion).map g ≫
        classifyingMap B hX hk f σ hσ T 0 (hasDegreeZero_zero B hX hk f σ hσ T) := by
      rw [e1, e2]
      congr 1
    apply Over.OverMorphism.ext
    have h := congrArg Over.Hom.left key
    simp only [Over.comp_left] at h ⊢
    have hg : ((Over.post (X := B.obj hk) B.inclusion).map g).left = p.left :=
      B.inclusion.map_preimage (X := B.obj hk) (Y := T.left) p.left
    rw [hg] at h
    exact h
  obtain ⟨N, hN⟩ := (classifyingMap_eq_classifyingMap_iff B hX hk f σ hσ T hx
    (hasDegreeZero_zero B hX hk f σ hσ T)).1 hcm
  exact ⟨N, hN.trans (sub_zero x)⟩

end Stacks.PicardFunctor
