module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Picard.TorsionSmoothProjectiveCurve.Degree
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Picard.Jacobian.DegreeBaseChange
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# The degree-zero part `Pic⁰_{X/k}` of the Picard functor of a curve

Let `X` be a proper scheme of dimension at most one over a field `k`, and let `Pic_{X/k}` be its
Picard functor on a big fppf site (`Stacks.PicardFunctor.picardFunctor`, [Stacks, Tag 0B9L]).
For a `k`-scheme `T` of the site and a point `t ∈ T`, restriction along `Spec κ(t) ⟶ T` carries
a section `ξ ∈ Pic_{X/k}(T)` to a section `ξ_t ∈ Pic_{X/k}(κ(t))` over the residue field.  The
*degree-zero part* `Pic⁰_{X/k}` is the subfunctor of those `ξ` all of whose fibres `ξ_t` are
classes of invertible modules of degree zero on `X_{κ(t)} = X ×_k κ(t)`:

`Pic⁰_{X/k}(T) = { ξ | ∀ t ∈ T, ξ_t = [ℒ] for an invertible ℒ on X_{κ(t)} with deg ℒ = 0 }`.

It is the subfunctor whose representing scheme is the component `Pic⁰_{X/k}` of [Stacks, Tag 0BA0],
clauses (1)–(3); this file only defines it and records that it is a subfunctor, which rests on
the invariance of the degree under extension of the ground field ([Stacks, Tag 0BY9]).

## Main definitions

* `Stacks.PicardFunctor.residueTest`: the test scheme `Spec κ(t) ⟶ Spec k` at a point `t` of a
  test scheme `T`, and `Stacks.PicardFunctor.residueTestι : residueTest T t ⟶ T`.
* `Stacks.PicardFunctor.fibreDegreeZero`: `Pic⁰(X_{κ(t)})`, the degree-zero classes on the fibre.
* `Stacks.PicardFunctor.degreeZeroSubfunctor`: **`Pic⁰_{X/k}`**, a `Subfunctor` of
  `picardFunctor B hX hk f`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9L](https://stacks.math.columbia.edu/tag/0B9L)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {k : Type u} [Field k] {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- **The residue test scheme at a point.** For a point `t` of (the scheme underlying) a test
scheme `T` over `k`, the scheme `Spec κ(t)` with its structure morphism
`Spec κ(t) ⟶ T ⟶ Spec k`, as a test scheme of the site. -/
abbrev residueTest (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : BigFppfOver B (Spec (.of k)) hk :=
  siteObject B (Spec (.of k)) hk (B.residueField_spec_contains T.left.property t)
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t ≫
      B.inclusion.map T.hom)

/-- The inclusion `Spec κ(t) ⟶ T` of the residue test scheme at a point. -/
def residueTestι (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) : residueTest B hk T t ⟶ T :=
  Over.homMk (ObjectProperty.homMk
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t)) rfl

/-- The map of residue test schemes induced by a morphism of test schemes:
`Spec κ(g t) ⟶`, read backwards, `Spec κ(t) ⟶ Spec κ(g t)`. -/
def residueTestMap {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueTest B hk T t ⟶
      residueTest B hk U ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t) :=
  Over.homMk (ObjectProperty.homMk
    (Spec.map (((BigFppfOver.toScheme B (Spec (.of k)) hk).map g).residueFieldMap t))) (by
      ext1
      change Spec.map (((BigFppfOver.toScheme B (Spec (.of k)) hk).map g).residueFieldMap t) ≫
          ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).fromSpecResidueField _ ≫
            B.inclusion.map U.hom =
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).fromSpecResidueField t ≫
          B.inclusion.map T.hom
      rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, ← Over.w g]
      rfl)

/-- The residue test schemes are compatible with a morphism of test schemes: going down to a
point of `T` and then along `g` is going to the image point of `U`. -/
theorem residueTestMap_comp_residueTestι {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    residueTestMap B hk g t ≫ residueTestι B hk U _ = residueTestι B hk T t ≫ g := by
  ext1
  ext1
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField _ t

/-- The underlying scheme of a residue test scheme has dimension at most one when `X` does: the
fibre `X ×_k κ(t)` has the dimension of `X` ([Stacks, Tag 0BY9], dimension clause). -/
theorem topologicalKrullDim_baseChange_residueTest [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    topologicalKrullDim (baseChange B hX hk f (residueTest B hk T t)) ≤ 1 := by
  have : Subsingleton (B.inclusion.obj (B.obj hk)) :=
    inferInstanceAs (Subsingleton (Spec (.of k)))
  have : Subsingleton (B.inclusion.obj (residueTest B hk T t).left) :=
    inferInstanceAs (Subsingleton
      (Spec (.of (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t))))
  have : Surjective (B.inclusion.map (residueTest B hk T t).hom) :=
    ⟨fun y => ⟨(default : Spec
      (.of (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t))),
      Subsingleton.elim _ _⟩⟩
  exact (topologicalKrullDim_eq_of_isPullback_of_subsingleton
    (IsPullback.of_hasPullback (B.inclusion.map f)
      (B.inclusion.map (residueTest B hk T t).hom))).trans_le hdim

/-- **`Pic⁰` of the fibre over a point.** The degree-zero classes on
`X_{κ(t)} = X ×_k κ(t)`, the fibre of the base change over the residue test scheme at `t`. -/
abbrev fibreDegreeZero [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)
    (T : BigFppfOver B (Spec (.of k)) hk)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    AddSubgroup (picardAt B hX hk f (residueTest B hk T t)) :=
  Stacks.Picard.ofSchemeDegreeZero
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t)
    (pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom))
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim T t)

/-- **The fibrewise degree-zero condition.** A section `ξ ∈ Pic_{X/k}(T)` has degree zero at every
point when, for each `t ∈ T`, its restriction to `Spec κ(t)` is the class of a degree-zero
invertible module on `X_{κ(t)}`. -/
def IsFibrewiseDegreeZero [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1)
    (T : BigFppfOver B (Spec (.of k)) hk) (ξ : (picardFunctor B hX hk f).obj (op T)) : Prop :=
  ∀ t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T,
    ∃ L ∈ fibreDegreeZero B hX hk f hdim T t,
      (toPicardFunctor B hX hk f).app (op (residueTest B hk T t)) L =
        (picardFunctor B hX hk f).map (residueTestι B hk T t).op ξ

/-- The base change of `X` to the residue test scheme at `t` is the base change of the base
change at `g t`: the square of base changes over `Spec κ(t) ⟶ Spec κ(g t)` is cartesian. -/
theorem isPullback_baseChangeMap_residueTestMap {T U : BigFppfOver B (Spec (.of k)) hk}
    (g : T ⟶ U) (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T) :
    IsPullback (baseChangeMap B hX hk f (residueTestMap B hk g t))
      (pullback.snd (B.inclusion.map f) (B.inclusion.map (residueTest B hk T t).hom))
      (pullback.snd (B.inclusion.map f)
        (B.inclusion.map (residueTest B hk U
          ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t)).hom))
      (B.inclusion.map (residueTestMap B hk g t).left) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (B.inclusion.map f)
      (B.inclusion.map (residueTest B hk U
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t)).hom))
    (v₁₃ := B.inclusion.map f)
    (h₂₂ := B.inclusion.map (residueTest B hk U
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t)).hom) ?_ ?_
    (IsPullback.of_hasPullback _ _)
  · have h := IsPullback.of_hasPullback (B.inclusion.map f)
      (B.inclusion.map (residueTest B hk T t).hom)
    convert h using 1
    · simp only [baseChangeMap, pullback.map, Category.comp_id]
      exact pullback.lift_fst _ _ _
    · rw [← Functor.map_comp, Over.w]
  · simp only [baseChangeMap, pullback.map]
    exact pullback.lift_snd _ _ _

/-- Restricting a degree-zero class of a fibre along the map of residue test schemes induced by a
morphism of test schemes gives a degree-zero class: the degree does not change under extension of
the ground field `κ(g t) ⟶ κ(t)`. -/
theorem picardMap_residueTestMap_mem_fibreDegreeZero [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    (t : (BigFppfOver.toScheme B (Spec (.of k)) hk).obj T)
    {L : picardAt B hX hk f
      (residueTest B hk U ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t))}
    (hL : L ∈ fibreDegreeZero B hX hk f hdim U
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t)) :
    picardMap B hX hk f (residueTestMap B hk g t) L ∈ fibreDegreeZero B hX hk f hdim T t := by
  let : Algebra (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t))
      (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t) :=
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).map g).residueFieldMap t).hom.toAlgebra
  have hsq := isPullback_baseChangeMap_residueTestMap B hX hk f g t
  have e : B.inclusion.map (residueTestMap B hk g t).left =
      Spec.map (CommRingCat.ofHom (algebraMap
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField
          ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t))
        (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t))) := rfl
  rw [e] at hsq
  rw [AddMonoidHom.mem_ker] at hL ⊢
  exact (Stacks.Picard.ofSchemeDegree_schemePullbackClass_of_isPullback
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).residueField
      ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t))
    (((BigFppfOver.toScheme B (Spec (.of k)) hk).obj T).residueField t) _ _ _ hsq
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim U _)
    (topologicalKrullDim_baseChange_residueTest B hX hk f hdim T t) L).trans hL

/-- **`Pic⁰_{X/k}` is a subfunctor**: the fibrewise degree-zero condition is stable under
restriction along morphisms of test schemes. -/
theorem isFibrewiseDegreeZero_map [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) {T U : BigFppfOver B (Spec (.of k)) hk} (g : T ⟶ U)
    {ξ : (picardFunctor B hX hk f).obj (op U)} (hξ : IsFibrewiseDegreeZero B hX hk f hdim U ξ) :
    IsFibrewiseDegreeZero B hX hk f hdim T ((picardFunctor B hX hk f).map g.op ξ) := by
  intro t
  obtain ⟨L, hL, hLξ⟩ := hξ ((BigFppfOver.toScheme B (Spec (.of k)) hk).map g t)
  refine ⟨_, picardMap_residueTestMap_mem_fibreDegreeZero B hX hk f hdim g t hL, ?_⟩
  rw [toPicardFunctor_app_naturality, hLξ, ← Functor.map_comp_apply,
    ← Functor.map_comp_apply]
  exact congrArg (fun φ => (picardFunctor B hX hk f).map φ ξ)
    (Quiver.Hom.unop_inj (residueTestMap_comp_residueTestι B hk g t))

/-- **`Pic⁰_{X/k}`, the degree-zero part of the Picard functor**: the subfunctor of
`Pic_{X/k}` of the sections whose restriction to every point `t` of the test scheme is the class
of a degree-zero invertible module on `X_{κ(t)}`. -/
def degreeZeroSubfunctor [IsProper (B.inclusion.map f)] (hdim : topologicalKrullDim X ≤ 1) :
    Subfunctor (picardFunctor B hX hk f) where
  obj T := {ξ | IsFibrewiseDegreeZero B hX hk f hdim T.unop ξ}
  map g _ hξ := isFibrewiseDegreeZero_map B hX hk f hdim g.unop hξ

/-- A section `ξ` of `Pic_{X/k}` over `T` lies in `Pic⁰_{X/k}` if and only if it is fibrewise
of degree zero. -/
theorem mem_degreeZeroSubfunctor_iff [IsProper (B.inclusion.map f)]
    (hdim : topologicalKrullDim X ≤ 1) (T : BigFppfOver B (Spec (.of k)) hk)
    (ξ : (picardFunctor B hX hk f).obj (op T)) :
    ξ ∈ (degreeZeroSubfunctor B hX hk f hdim).obj (op T) ↔
      IsFibrewiseDegreeZero B hX hk f hdim T ξ :=
  Iff.rfl

end Stacks.PicardFunctor

end
