module

public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RigidifiedPicardFunctor

/-!
# The degree-zero part of the rigidified Picard functor of a proper relative curve

Let `f : X ⟶ S` be proper and locally of finite type with fibres of dimension at most one, and
let `σ` be a section of `f`. For an `S`-scheme `T` the base change `X_T ⟶ T` is again such a
morphism, so a Picard class of `X_T` has a degree on every fibre
(`AlgebraicGeometry.relativeInvertibleDegreeHom`). The rigidified classes of degree zero on every
fibre form a subfunctor `Pic⁰_{X/S,σ}` of the rigidified Picard functor
`Stacks.RigidifiedPicard.functor`, and it is again a Zariski sheaf: the degree is natural in `T`
and a point of `T` lies in some member of any Zariski covering.

This is the functor whose representability [Stacks, Tag 0BA0] (3) expresses as the
degree-zero subgroup scheme `Pic⁰_{X/k}`, and to which the group-scheme criterion
`AlgebraicGeometry.exists_grp_iso_of_representable_openSubfunctor` ([Stacks, Tag 0B9Q]) is
applied.

## Main definitions

* `Stacks.RigidifiedPicard.degree` — the degree of a small Picard class of `X_T`, a function on
  `T`.
* `Stacks.RigidifiedPicard.groupZero` — the rigidified classes of degree zero on every fibre.
* `Stacks.RigidifiedPicard.functorZero` — `Pic⁰_{X/S,σ}`, as a functor to groups.

## Main results

* `Stacks.RigidifiedPicard.topologicalKrullDim_fiber_bcProj_le` — the fibres of `X_T ⟶ T` have
  dimension at most one.
* `Stacks.RigidifiedPicard.degree_smallSchemePullbackClassHom_bcMap` — naturality of the degree.
* `Stacks.RigidifiedPicard.isSheaf_functorZero` — the Zariski sheaf property.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0B9Q](https://stacks.math.columbia.edu/tag/0B9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The fibres of a base change of a relative curve are curves.** -/
theorem topologicalKrullDim_fiber_bcProj_le [LocallyOfFiniteType f]
    (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (T : Over S) (t : T.left) :
    topologicalKrullDim ↥((bcProj f T).fiber t) ≤ 1 := by
  let : Algebra (S.residueField (T.hom t)) (T.left.residueField t) :=
    (T.hom.residueFieldMap t).hom.toAlgebra
  have h := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f T.hom) t
  have hlft : LocallyOfFiniteType (f.fiberToSpecResidueField (T.hom t)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType)
      (IsPullback.of_hasPullback f (S.fromSpecResidueField (T.hom t))) inferInstance
  exact (@topologicalKrullDim_baseChange (S.residueField (T.hom t)) (T.left.residueField t)
    _ _ _ _ _ _ _ _ h hlft).trans_le (hdim _)

variable [IsProper f] [LocallyOfFiniteType f] (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1)

/-- The base change `X_T ⟶ T` of a proper morphism is proper. -/
instance isProper_bcProj (T : Over S) : IsProper (bcProj f T) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback f T.hom) inferInstance

/-- **The degree of a small Picard class of `X_T`**, as the function on `T` recording its degree
on each fibre of `X_T ⟶ T`. -/
def degree (T : Over S) : Stacks.Picard.smallOfScheme (bc f T) →+ (T.left → ℤ) :=
  (relativeInvertibleDegreeHom (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T)).comp
    (smallEquiv (bc f T)).toAddMonoidHom

/-- The value of `degree` at a point `t` of `T` is the degree of the class on the fibre over
`t`. -/
theorem degree_apply (T : Over S) (x : Stacks.Picard.smallOfScheme (bc f T)) (t : T.left) :
    degree f hdim T x t =
      relativeInvertibleDegreeHomAt (bcProj f T) (topologicalKrullDim_fiber_bcProj_le f hdim T) t
        (smallEquiv (bc f T) x) :=
  rfl

/-- **The degree is natural in the base.** -/
theorem degree_smallSchemePullbackClassHom_bcMap {T U : Over S} (g : T ⟶ U)
    (x : Stacks.Picard.smallOfScheme (bc f U)) :
    degree f hdim T (Stacks.Picard.smallSchemePullbackClassHom (bcMap f g) x) =
      degree f hdim U x ∘ g.left := by
  simp only [degree, AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    smallEquiv_smallSchemePullbackClassHom]
  exact relativeInvertibleDegreeHom_schemePullbackClass_of_isPullback (bcMap_isPullback_proj f g)
    _ _ _

variable (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)

/-- **`Pic⁰_{X/S,σ}(T)`**: the rigidified classes of degree zero on every fibre of `X_T ⟶ T`. -/
def groupZero (T : Over S) : AddSubgroup (group f σ hσ T) :=
  ((degree f hdim T).comp (group f σ hσ T).subtype).ker

/-- A rigidified class lies in `groupZero` if and only if its degree vanishes at every point of
`T`. -/
theorem mem_groupZero_iff (T : Over S) (x : group f σ hσ T) :
    x ∈ groupZero f hdim σ hσ T ↔ ∀ t : T.left, degree f hdim T x t = 0 := by
  rw [groupZero, AddMonoidHom.mem_ker, funext_iff]
  rfl

/-- Pullback along a morphism of `S`-schemes preserves rigidified classes of degree zero. -/
theorem groupMap_mem_groupZero {T U : Over S} (g : T ⟶ U) (x : group f σ hσ U)
    (hx : x ∈ groupZero f hdim σ hσ U) : groupMap f σ hσ g x ∈ groupZero f hdim σ hσ T := by
  rw [mem_groupZero_iff] at hx ⊢
  intro t
  rw [coe_groupMap, degree_smallSchemePullbackClassHom_bcMap]
  exact hx _

/-- **The degree-zero rigidified Picard functor `Pic⁰_{X/S,σ}`**, on all `S`-schemes, valued in
groups. -/
abbrev functorZero : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  subfunctor f σ hσ (groupZero f hdim σ hσ) fun g x hx => groupMap_mem_groupZero f hdim σ hσ g x hx

/-- **`Pic⁰_{X/S,σ}` is a Zariski sheaf**, as soon as the structure sheaf of every `S`-scheme
is the direct image of the structure sheaf of its base change. -/
theorem isSheaf_functorZero (hOiso : ∀ U : Over S, IsIso (bcProj f U).toLRSHom.toHom.c) :
    Presheaf.IsSheaf (Scheme.zariskiTopology.over S) (functorZero f hdim σ hσ ⋙ forget GrpCat) := by
  refine isSheaf_subfunctor f σ hσ hOiso _ _ fun {T ι U} g hg x hx => ?_
  rw [Scheme.ofArrows_mem_precoverage_iff] at hg
  rw [mem_groupZero_iff]
  intro t
  obtain ⟨i, u, rfl⟩ := hg.1 t
  have h := (mem_groupZero_iff f hdim σ hσ (U i) _).1 (hx i) u
  rwa [coe_groupMap, degree_smallSchemePullbackClassHom_bcMap] at h

end Stacks.RigidifiedPicard

end
