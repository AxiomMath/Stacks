/-
Copyright (c) 2026 Stacks Project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.JacobianPointGroup
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.DegreeComponentProper
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapComponent
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition

/-!
# Classifying maps into the Jacobian, and the Abel–Jacobi map of a pointed curve

Let `X` be a smooth projective curve over a field `k` with a rational point `c₀`, whose Picard
functor is representable, and let `J = Pic^0_{X/k}` be its Jacobian
(`Stacks.PicardFunctor.jacobianGrp`). A morphism `T ⟶ J` from a test scheme is the same as a
point of the Picard functor over `T` all of whose fibres have degree zero
(`Stacks.PicardFunctor.jacobianHomAddEquiv`), and every such point is the class of an invertible
module on `X ×_k T` ([Stacks, Tag 0B9N]). This file packages that correspondence as the
*classifying map* `classifyingMap T x : T ⟶ J` of a class `x ∈ Pic(X ×_k T)` with degree-zero
fibres, with its formal properties:

* it is additive in `x` and natural in `T`;
* two classes have the same classifying map exactly when they differ by the pullback of a class
  on `T` (the seesaw principle, from the exactness of `0 → Pic(T) → Pic(X_T) → Pic_{X/k}(T)`).

The **Abel–Jacobi map** `aj : X ⟶ J`, `c ↦ 𝒪(c - c₀)`, is the classifying map, over `T = X`, of
the class `[𝒪(Δ)] - [𝒪({c₀} × X)]` on `X ×_k X`: the diagonal `Δ` and the constant section
`{c₀} × X` are degree-one families over the second factor, so their difference has degree zero on
every fibre.

## Main definitions

* `Stacks.PicardFunctor.classifyingMap`: the morphism `T ⟶ J` of a class with degree-zero fibres.
* `Stacks.PicardFunctor.curveObj`: the curve `X` as a test scheme over `k`.
* `Stacks.PicardFunctor.diagonalFamily`, `Stacks.PicardFunctor.constantFamily`: the degree-one
  families `Δ` and `{c₀} × X` in `X ×_k X` over the second factor.
* `Stacks.PicardFunctor.abelJacobi`: the Abel–Jacobi map `X ⟶ J`.

## Main results

* `Stacks.PicardFunctor.classifyingMap_add`, `Stacks.PicardFunctor.classifyingMap_comp`.
* `Stacks.PicardFunctor.classifyingMap_eq_classifyingMap_iff`: the seesaw principle.
* `Stacks.PicardFunctor.jacobianHomAddEquiv_abelJacobi`: the defining property of `aj`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

/-! ### Classifying maps -/

/-- A class on `X ×_k T` *has degree zero* when its point of the Picard functor lies in the
degree-zero subgroup: every fibre has degree zero. -/
abbrev HasDegreeZero (T : BigFppfOver B (Spec (.of k)) hk) (x : picardAt B hX hk f T) : Prop :=
  toPicardFunctorHom B hX hk f T x ∈ degreeZeroAddSubgroup B hX hk f σ hσ T

/-- **The classifying map `T ⟶ J` of a class on `X ×_k T` with degree-zero fibres.** -/
def classifyingMap (T : BigFppfOver B (Spec (.of k)) hk) (x : picardAt B hX hk f T)
    (hx : HasDegreeZero B hX hk f σ hσ T x) :
    (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  Additive.toMul ((jacobianHomAddEquiv B hX hk f σ hσ T).symm ⟨_, hx⟩)

/-- Under `jacobianHomAddEquiv`, the classifying map of `x` corresponds to the point of the
Picard functor defined by `x`. -/
theorem jacobianHomAddEquiv_classifyingMap (T : BigFppfOver B (Spec (.of k)) hk)
    (x : picardAt B hX hk f T) (hx : HasDegreeZero B hX hk f σ hσ T x) :
    jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul (classifyingMap B hX hk f σ hσ T x hx)) =
      ⟨_, hx⟩ := by
  rw [classifyingMap, ofMul_toMul, AddEquiv.apply_symm_apply]

/-- Every morphism `T ⟶ J` is a classifying map. -/
theorem exists_classifyingMap_eq (T : BigFppfOver B (Spec (.of k)) hk)
    (ψ : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ (jacobianGrp B hX hk f σ hσ).X) :
    ∃ (x : picardAt B hX hk f T) (hx : HasDegreeZero B hX hk f σ hσ T x),
      classifyingMap B hX hk f σ hσ T x hx = ψ := by
  set z := jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)
  obtain ⟨x, hxz⟩ := surjective_toPicardFunctorHom B hX hk f σ hσ
    (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T z.1
  have hx : HasDegreeZero B hX hk f σ hσ T x := by
    rw [HasDegreeZero, hxz]
    exact z.2
  refine ⟨x, hx, ?_⟩
  rw [classifyingMap]
  rw [show (⟨_, hx⟩ : degreeZeroAddSubgroup B hX hk f σ hσ T) = z from Subtype.ext hxz,
    AddEquiv.symm_apply_apply, toMul_ofMul]

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The sum of two classes with degree-zero fibres has degree-zero fibres. -/
theorem hasDegreeZero_add {T : BigFppfOver B (Spec (.of k)) hk} {x y : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) (hy : HasDegreeZero B hX hk f σ hσ T y) :
    HasDegreeZero B hX hk f σ hσ T (x + y) := by
  simpa [HasDegreeZero] using add_mem hx hy

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The negative of a class with degree-zero fibres has degree-zero fibres. -/
theorem hasDegreeZero_neg {T : BigFppfOver B (Spec (.of k)) hk} {x : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) :
    HasDegreeZero B hX hk f σ hσ T (-x) := by
  simpa [HasDegreeZero] using neg_mem hx

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The difference of two classes with degree-zero fibres has degree-zero fibres. -/
theorem hasDegreeZero_sub {T : BigFppfOver B (Spec (.of k)) hk} {x y : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) (hy : HasDegreeZero B hX hk f σ hσ T y) :
    HasDegreeZero B hX hk f σ hσ T (x - y) := by
  simpa [HasDegreeZero] using sub_mem hx hy

/-- Two morphisms `T ⟶ J` are equal when their classes in the Picard functor are. -/
private theorem eq_of_jacobianHomAddEquiv_eq (T : BigFppfOver B (Spec (.of k)) hk)
    {ψ ψ' : (Over.post (X := B.obj hk) B.inclusion).obj T ⟶ (jacobianGrp B hX hk f σ hσ).X}
    (h : jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ) =
      jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ')) : ψ = ψ' :=
  Additive.ofMul.injective ((jacobianHomAddEquiv B hX hk f σ hσ T).injective h)

/-- **Classifying maps are additive.** -/
theorem classifyingMap_add (T : BigFppfOver B (Spec (.of k)) hk) {x y : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) (hy : HasDegreeZero B hX hk f σ hσ T y) :
    classifyingMap B hX hk f σ hσ T (x + y) (hasDegreeZero_add B hX hk f σ hσ hx hy) =
      classifyingMap B hX hk f σ hσ T x hx * classifyingMap B hX hk f σ hσ T y hy := by
  apply eq_of_jacobianHomAddEquiv_eq B hX hk f σ hσ T
  rw [ofMul_mul, map_add, jacobianHomAddEquiv_classifyingMap, jacobianHomAddEquiv_classifyingMap,
    jacobianHomAddEquiv_classifyingMap]
  exact Subtype.ext (map_add _ x y)

/-- **The seesaw principle.** Two classes on `X ×_k T` with degree-zero fibres have the same
classifying map exactly when they differ by the pullback of a class on `T`. -/
theorem classifyingMap_eq_classifyingMap_iff (T : BigFppfOver B (Spec (.of k)) hk)
    {x y : picardAt B hX hk f T}
    (hx : HasDegreeZero B hX hk f σ hσ T x) (hy : HasDegreeZero B hX hk f σ hσ T y) :
    classifyingMap B hX hk f σ hσ T x hx = classifyingMap B hX hk f σ hσ T y hy ↔
      ∃ N : Stacks.Picard.ofScheme ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T),
        Stacks.Picard.schemePullbackClass (baseChangeProj B hX hk f T) N = x - y := by
  have hex := exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom B hX hk f σ hσ
    (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T (x - y)
  show _ ↔ x - y ∈ Set.range _
  rw [← hex, map_sub, sub_eq_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa only [jacobianHomAddEquiv_classifyingMap] using
      congrArg (fun ψ => (jacobianHomAddEquiv B hX hk f σ hσ T (Additive.ofMul ψ)).1) h
  · apply eq_of_jacobianHomAddEquiv_eq B hX hk f σ hσ T
    rw [jacobianHomAddEquiv_classifyingMap, jacobianHomAddEquiv_classifyingMap]
    exact Subtype.ext h

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The pullback along `T' ⟶ T` of a class with degree-zero fibres has degree-zero fibres. -/
theorem hasDegreeZero_picardMap {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    {x : picardAt B hX hk f T} (hx : HasDegreeZero B hX hk f σ hσ T x) :
    HasDegreeZero B hX hk f σ hσ T' (picardMap B hX hk f g x) := by
  have h := (degreeZeroMap B hX hk f σ hσ g ⟨_, hx⟩).2
  change (picardFunctor B hX hk f).map g.op ((toPicardFunctor B hX hk f).app (op T) x) ∈ _ at h
  rw [HasDegreeZero, toPicardFunctorHom_apply, toPicardFunctor_app_naturality]
  exact h

/-- **Classifying maps are natural in the test scheme.** -/
theorem classifyingMap_comp {T T' : BigFppfOver B (Spec (.of k)) hk} (g : T' ⟶ T)
    (x : picardAt B hX hk f T) (hx : HasDegreeZero B hX hk f σ hσ T x) :
    (Over.post (X := B.obj hk) B.inclusion).map g ≫ classifyingMap B hX hk f σ hσ T x hx =
      classifyingMap B hX hk f σ hσ T' (picardMap B hX hk f g x)
        (hasDegreeZero_picardMap B hX hk f σ hσ g hx) := by
  apply eq_of_jacobianHomAddEquiv_eq B hX hk f σ hσ T'
  refine (jacobianHomAddEquiv_comp B hX hk f σ hσ g
    (classifyingMap B hX hk f σ hσ T x hx)).trans ?_
  rw [jacobianHomAddEquiv_classifyingMap, jacobianHomAddEquiv_classifyingMap]
  apply Subtype.ext
  show (picardFunctor B hX hk f).map g.op ((toPicardFunctor B hX hk f).app (op T) x) =
    (toPicardFunctor B hX hk f).app (op T') (picardMap B hX hk f g x)
  rw [toPicardFunctor_app_naturality]
  rfl

/-! ### The Abel–Jacobi map -/

/-- The curve `X` as a test scheme over `k`. -/
abbrev curveObj : BigFppfOver B (Spec (.of k)) hk := Over.mk f

/-- The curve `X` as a scheme over `k`. -/
abbrev curveOver : Over (Spec (.of k)) := Over.mk (B.inclusion.map f)

include hσ in
/-- The constant relative point `X ⟶ X`, `c ↦ c₀`, over `k`. -/
def constantPoint : curveOver B hX hk f ⟶ curveOver B hX hk f :=
  Over.homMk (B.inclusion.map f ≫ σ) <| by
    change (B.inclusion.map f ≫ σ) ≫ B.inclusion.map f = B.inclusion.map f
    rw [Category.assoc, hσ]
    exact Category.comp_id _

/-- The structure morphism `X ⟶ Spec k` is separated. -/
instance isSeparated_curveOver_hom : IsSeparated (curveOver B hX hk f).hom :=
  inferInstanceAs (IsSeparated (B.inclusion.map f))

/-- **The diagonal `Δ ⊂ X ×_k X`, a degree-one family over the second factor**: the graph of the
identity relative point. -/
def diagonalFamily :
    Stacks.Hilbert.HilbertFamily (curveOver B hX hk f)
      (Over.mk (B.inclusion.map (curveObj B hX hk f).hom)) 1 where
  ideal := Stacks.Hilbert.pointIdeal (curveOver B hX hk f) (curveOver B hX hk f) (𝟙 _)
  isFiniteLocallyFreeOfRank :=
    haveI := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
      (curveOver B hX hk f) (𝟙 _)
    Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal _ _ _

/-- **The constant section `{c₀} × X ⊂ X ×_k X`, a degree-one family over the second factor.** -/
def constantFamily :
    Stacks.Hilbert.HilbertFamily (curveOver B hX hk f)
      (Over.mk (B.inclusion.map (curveObj B hX hk f).hom)) 1 where
  ideal := Stacks.Hilbert.pointIdeal (curveOver B hX hk f) (curveOver B hX hk f)
    (constantPoint B hX hk f σ hσ)
  isFiniteLocallyFreeOfRank :=
    haveI := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated (curveOver B hX hk f)
      (curveOver B hX hk f) (constantPoint B hX hk f σ hσ)
    Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal _ _ _

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The fibre degree of the point of a degree-`d` family is `d`. -/
theorem curveFibreDegree_familyClass {d : ℕ} (T : BigFppfOver B (Spec (.of k)) hk)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    curveFibreDegree B hX hk f σ hσ T (toPicardFunctorHom B hX hk f T D.picardClass) t = d :=
  Stacks.AbelMap.toPicardFunctor_picardClass_mem B hX hk f
    (isDegreeComponent_curveDegreeSubfunctor B hX hk f σ hσ d) T D t

omit [(picardFunctor B hX hk f).IsRepresentable] in
/-- The difference of the classes of two families of the same degree has degree zero. -/
theorem hasDegreeZero_familyClass_sub {d : ℕ} (T : BigFppfOver B (Spec (.of k)) hk)
    (D D' : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) :
    HasDegreeZero B hX hk f σ hσ T (D.picardClass - D'.picardClass) := by
  intro t
  have h := fibreDegree_add B hX hk f σ hσ (isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ) T
    (toPicardFunctorHom B hX hk f T (D.picardClass - D'.picardClass))
    (toPicardFunctorHom B hX hk f T D'.picardClass) t
  rw [← map_add, sub_add_cancel] at h
  have h1 := curveFibreDegree_familyClass B hX hk f σ hσ T D t
  have h2 := curveFibreDegree_familyClass B hX hk f σ hσ T D' t
  show curveFibreDegree B hX hk f σ hσ T _ t = 0
  simp only [curveFibreDegree] at h1 h2 ⊢
  rw [h1, h2] at h
  omega

/-- The class `[𝒪(Δ)] - [𝒪({c₀} × X)]` on `X ×_k X`. -/
abbrev abelJacobiClass : picardAt B hX hk f (curveObj B hX hk f) :=
  (diagonalFamily B hX hk f).picardClass - (constantFamily B hX hk f σ hσ).picardClass

/-- **The Abel–Jacobi map `aj : X ⟶ J`, `c ↦ 𝒪(c - c₀)`**: the classifying map of
`[𝒪(Δ)] - [𝒪({c₀} × X)]` on `X ×_k X`, a family of degree-zero invertible modules over the
second factor. -/
def abelJacobi : curveOver B hX hk f ⟶ (jacobianGrp B hX hk f σ hσ).X :=
  classifyingMap B hX hk f σ hσ (curveObj B hX hk f) (abelJacobiClass B hX hk f σ hσ)
    (hasDegreeZero_familyClass_sub B hX hk f σ hσ _ _ _)

end Stacks.PicardFunctor
