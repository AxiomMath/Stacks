module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.PicardScheme.BaseChangePullback
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctorDegree

/-!
# The degree components of the Picard presheaf of a proper relative curve are subfunctors

Let `f : X ⟶ S` be a morphism of a big fppf site which is proper with fibres of dimension at most
one. For every test scheme `T` the base change `X_T ⟶ T` is again such a morphism, so every class
of `Pic(X_T)` has a degree function `T → ℤ`
(`Stacks.PicardFunctor.picardDegreeHom`). This file proves that the degree function is natural in
`T`: pulling a class back along `a : T ⟶ U` composes its degree function with `a`. Consequently,
for each integer `d`, the classes of constant degree `d` form a subfunctor

`Pic^d ⊂ (T ↦ Pic(X_T))`

of the presheaf whose fppf sheafification is the Picard functor. This is the functor-level
content of the decomposition `Pic_{X/k} = ⨆_d Pic^d_{X/k}` in clause (1) of [Stacks, Tag 0BA0].

## Main results

* `Stacks.PicardFunctor.topologicalKrullDim_fiber_baseChangeProj_le` — the fibres of `X_T ⟶ T`
  have dimension at most one when those of `X ⟶ S` do.
* `Stacks.PicardFunctor.picardDegreeHom_picardMap` — the degree function is natural in the test
  scheme.
* `Stacks.PicardFunctor.picardDegreeSubfunctor` — `Pic^d`, as a subfunctor of the Picard
  presheaf.
* `Stacks.PicardFunctor.picardFunctorDegreeSubfunctor` — `Pic^d_{X/S}`, as a subfunctor of the
  Picard functor: the classes which are fppf locally of degree `d`; it is an fppf sheaf
  (`Stacks.PicardFunctor.isSheaf_picardFunctorDegreeSubfunctor`).

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS)

/-- **The fibres of a base change of a relative curve are curves.** If every fibre of `X ⟶ S`
has dimension at most one and `X ⟶ S` is locally of finite type, then every fibre of the base
change `X_T ⟶ T` along a test scheme `T` has dimension at most one. -/
theorem topologicalKrullDim_fiber_baseChangeProj_le [LocallyOfFiniteType (B.inclusion.map f)]
    (hdim : ∀ s : ↥(B.inclusion.obj (B.obj hS)),
      topologicalKrullDim ↥((B.inclusion.map f).fiber s) ≤ 1)
    (T : BigFppfOver B S hS) (t : ↥((BigFppfOver.toScheme B S hS).obj T)) :
    topologicalKrullDim ↥((baseChangeProj B hX hS f T).fiber t) ≤ 1 := by
  let : Algebra ((B.inclusion.obj (B.obj hS)).residueField (B.inclusion.map T.hom t))
      (((BigFppfOver.toScheme B S hS).obj T).residueField t) :=
    ((B.inclusion.map T.hom).residueFieldMap t).hom.toAlgebra
  have h := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback (B.inclusion.map f) (B.inclusion.map T.hom)) t
  have hlft : LocallyOfFiniteType
      ((B.inclusion.map f).fiberToSpecResidueField (B.inclusion.map T.hom t)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback (B.inclusion.map f)
        ((B.inclusion.obj (B.obj hS)).fromSpecResidueField (B.inclusion.map T.hom t)))
      (inferInstanceAs (LocallyOfFiniteType (B.inclusion.map f)))
  exact (@topologicalKrullDim_baseChange
    ((B.inclusion.obj (B.obj hS)).residueField (B.inclusion.map T.hom t))
    (((BigFppfOver.toScheme B S hS).obj T).residueField t) _ _ _ _ _ _ _ _ h hlft).trans_le
      (hdim _)

/-- **The degree of a Picard class is natural in the test scheme.** For a morphism `a : T ⟶ U`
of test schemes and a class `x` of `Pic(X_U)`, the degree function of the pullback of `x` to
`X_T` is the degree function of `x` composed with `a`. -/
theorem picardDegreeHom_picardMap {T U : BigFppfOver B S hS} (a : T ⟶ U)
    [IsProper (baseChangeProj B hX hS f T)] [IsProper (baseChangeProj B hX hS f U)]
    (hdimT : ∀ t : ↥((BigFppfOver.toScheme B S hS).obj T),
      topologicalKrullDim ↥((baseChangeProj B hX hS f T).fiber t) ≤ 1)
    (hdimU : ∀ u : ↥((BigFppfOver.toScheme B S hS).obj U),
      topologicalKrullDim ↥((baseChangeProj B hX hS f U).fiber u) ≤ 1)
    (x : picardAt B hX hS f U) :
    picardDegreeHom B hX hS f T hdimT (picardMap B hX hS f a x) =
      picardDegreeHom B hX hS f U hdimU x ∘ (B.inclusion.map a.left) :=
  relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback
    (baseChangeMap_isPullback_proj B hX hS f a) hdimU hdimT x

variable [hf : IsProper (B.inclusion.map f)]
  (hdim : ∀ s : ↥(B.inclusion.obj (B.obj hS)),
    topologicalKrullDim ↥((B.inclusion.map f).fiber s) ≤ 1)

/-- **`Pic^d` as a subfunctor of the Picard presheaf.** For a proper morphism `X ⟶ S` of the big
fppf site whose fibres have dimension at most one, and an integer `d`, the classes of `Pic(X_T)`
of degree `d` on every fibre of `X_T ⟶ T`, for `T` running over the test schemes, form a
subfunctor of `T ↦ Pic(X_T)`. -/
def picardDegreeSubfunctor (d : ℤ) : Subfunctor (picardPresheaf B hX hS f) where
  obj T :=
    haveI := isProper_baseChangeProj B hX hS f hf T.unop
    picardDegreeComponentConst B hX hS f T.unop
      (topologicalKrullDim_fiber_baseChangeProj_le B hX hS f hdim T.unop) d
  map {U T} a x hx := by
    have := isProper_baseChangeProj B hX hS f hf T.unop
    have := isProper_baseChangeProj B hX hS f hf U.unop
    exact (mem_picardDegreeComponentConst_iff B hX hS f T.unop _ d _).2 fun t =>
      (congrFun (picardDegreeHom_picardMap B hX hS f a.unop _
        (topologicalKrullDim_fiber_baseChangeProj_le B hX hS f hdim U.unop) x) t).trans
          ((mem_picardDegreeComponentConst_iff B hX hS f U.unop _ d x).1 hx _)

/-- Membership in `Pic^d(T)` is having degree `d` on every fibre of `X_T ⟶ T`. -/
theorem mem_picardDegreeSubfunctor_obj_iff (d : ℤ) (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T) :
    haveI := isProper_baseChangeProj B hX hS f hf T
    x ∈ (picardDegreeSubfunctor B hX hS f hdim d).obj (Opposite.op T) ↔
      ∀ t : ↥((BigFppfOver.toScheme B S hS).obj T),
        picardDegreeHom B hX hS f T
          (topologicalKrullDim_fiber_baseChangeProj_le B hX hS f hdim T) x t = d :=
  mem_picardDegreeComponentConst_iff B hX hS f T _ d x

/-- **`Pic^d_{X/S}` as a subfunctor of the Picard functor.** The elements of `Pic_{X/S}(T)` which
are, fppf locally on `T`, the image of a class of `Pic(X_T)` of degree `d` on every fibre: the
fppf sheafification, inside the sheaf `Pic_{X/S}`, of the image of `Pic^d` of the presheaf. -/
def picardFunctorDegreeSubfunctor (d : ℤ) : Subfunctor (picardFunctor B hX hS f) :=
  ((picardDegreeSubfunctor B hX hS f hdim d).image (toPicardFunctor B hX hS f)).sheafify
    (BigFppfOver.topology B S hS)

/-- `Pic^d_{X/S}` is an fppf sheaf. -/
theorem isSheaf_picardFunctorDegreeSubfunctor (d : ℤ) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS)
      (picardFunctorDegreeSubfunctor B hX hS f hdim d).toFunctor :=
  Subfunctor.sheafify_isSheaf _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (isSheaf_picardFunctor B hX hS f))

/-- The class in `Pic_{X/S}(T)` of a class of `Pic(X_T)` of degree `d` lies in `Pic^d_{X/S}(T)`. -/
theorem toPicardFunctor_mem_picardFunctorDegreeSubfunctor (d : ℤ) (T : BigFppfOver B S hS)
    (x : picardAt B hX hS f T)
    (hx : x ∈ (picardDegreeSubfunctor B hX hS f hdim d).obj (Opposite.op T)) :
    (toPicardFunctor B hX hS f).app (Opposite.op T) x ∈
      (picardFunctorDegreeSubfunctor B hX hS f hdim d).obj (Opposite.op T) :=
  Subfunctor.le_sheafify _ _ _ ⟨x, hx, rfl⟩

end Stacks.PicardFunctor

end
