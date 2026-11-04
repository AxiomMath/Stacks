module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.Vocabulary
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PropertyGammaPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Cycles on a represented algebraic space and on the representing scheme

Let `U` be a scheme of the big fppf site of `S`, and let `X = h_U` be the algebraic space it
represents. The points of `X` are the points of `U`, with the same topology (Stacks 03BX). This
file shows that the cycle theory of `X` as an algebraic space, in the sense of Chapter 82 of the
Stacks Project, is the cycle theory of `U` as a scheme, in the sense of Chapter 42.

* The integral closed subspaces of `X` correspond to the points of `U`: an integral closed
  subspace `Z ⊆ X` corresponds to the generic point of its set of points, read in `U`. In the
  scheme theory a point `x` of `U` stands for the integral closed subscheme `closure {x}` with
  its reduced structure, so this is the bijection between integral closed subspaces of `X` and
  integral closed subschemes of `U`. Under it the set of points of `Z` is the closure of the
  corresponding point.
* Suppose `X` is good over the base `B` of Situation 0EDT through `s_X : X → B`, and let
  `(C.S, δ)` be a base situation of Chapter 42 with a morphism `s₀ : U → C.S` locally of finite
  type. When the dimension function `δ_{U/C.S}` of Stacks 02JW agrees with `δ_{X/B}` of Stacks
  0EDT under the identification of points — the predicate
  `AlgebraicGeometry.Space.IsDeltaCompatible` — the bijection preserves δ-dimension, and
  sending a cycle `∑ n_Z [Z]` on `X` to the cycle on `U` with the same coefficients is an
  isomorphism `Z_k(X) ≅ Z_k(U)` for every `k`.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.schemeGenericPoint`: the generic point of an
  integral closed subspace of `h_U`, as a point of `U`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.equivSchemePoints`: the bijection between the
  integral closed subspaces of `h_U` and the points of `U`.
* `AlgebraicGeometry.Space.IsDeltaCompatible`: the dimension function of a scheme situation
  computes, on `U`, the dimension function of the good space `h_U`.
* `AlgebraicGeometry.Space.cycleGroupEquivScheme`: the isomorphism `Z_k(h_U) ≅ Z_k(U)`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.image_subspacePointSet`: the set of points of
  `Z`, read in `U`, is the closure of the generic point of `Z`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.bijective_schemeGenericPoint`: every point of
  `U` is the generic point of exactly one integral closed subspace of `h_U`.
* `AlgebraicGeometry.Space.deltaDimension_eq_schemeDeltaDimension`: the δ-dimension of an
  integral closed subspace of `h_U` is the δ-dimension of the corresponding integral closed
  subscheme of `U`.
* `AlgebraicGeometry.Space.locallyFinite_iff_locallyFiniteSupport`: the local finiteness
  condition of Stacks 0EDZ on a family of coefficients is the local finiteness of the support
  of the corresponding function on `U`, which is the condition of Stacks 02QR.
* `AlgebraicGeometry.Space.mem_cyclesOfDimension_iff_mem_scheme`: a family of coefficients is
  a `k`-cycle on `h_U` exactly when the corresponding function is a `k`-cycle on `U`.

## Implementation notes

The scheme-side base situation is a parameter rather than a construction. The base `B` of
Situation 0EDT is an algebraic space, so the scheme theory of `U` has to be set up over some
scheme, and the comparison only needs that the two dimension functions agree on `U`; this is
the content of `AlgebraicGeometry.Space.IsDeltaCompatible`, which takes a value at every point
and is checked pointwise.

Both cycle theories are indexed so that the comparison is a reindexing of coefficients: the
cycles of Stacks 0EDZ are indexed by integral closed subspaces, those of Stacks 02QR, through
Mathlib's `AlgebraicGeometry.AlgebraicCycle`, by points. The bijection between the two index
sets is Stacks 0ENF for the decent space `h_U` composed with Stacks 03BX.

## References

* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Integral closed subspaces of a represented space and points of the scheme -/

section Points

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The generic point of an integral closed subspace `Z` of the algebraic space `h_U`
represented by `U`, as a point of the scheme `U`. -/
def IntegralClosedSubspace.schemeGenericPoint
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) : (BigFppfOver.toScheme B S hS).obj U :=
  pointsToScheme B S hS U
    (pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS))

/-- The set of points of an integral closed subspace of `h_U`, read in `U`, is the closure of
its generic point. -/
theorem IntegralClosedSubspace.image_subspacePointSet
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    pointsToScheme B S hS U '' subspacePointSet B S hS (yoneda.obj U) Z.subspace =
      closure {Z.schemeGenericPoint B S hS U} := by
  rw [← isGenericPoint_def.1
    (isGenericPoint_pointsMap_genericPoint B S hS (isAlgebraicSpace_yoneda B S hS U) Z)]
  have := (schemePointsHomeomorph B S hS U).image_closure
    {pointsMap B S hS Z.subspace.toFunctor Z.subspace.ι (Z.genericPoint B S hS)}
  rwa [Set.image_singleton] at this

/-- A point of `h_U` lies in an integral closed subspace exactly when the corresponding point
of `U` specializes from the generic point of that subspace. -/
theorem IntegralClosedSubspace.mem_subspacePointSet_iff
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) (p : points B S hS (yoneda.obj U)) :
    p ∈ subspacePointSet B S hS (yoneda.obj U) Z.subspace ↔
      pointsToScheme B S hS U p ∈ closure {Z.schemeGenericPoint B S hS U} := by
  rw [← Z.image_subspacePointSet B S hS U,
    (injective_pointsToScheme B S hS U).mem_set_image]

/-- Distinct integral closed subspaces of `h_U` have distinct generic points in `U`: an
integral closed subspace is determined by its set of points, Stacks 0ENF. -/
theorem IntegralClosedSubspace.injective_schemeGenericPoint :
    Function.Injective (IntegralClosedSubspace.schemeGenericPoint B S hS U) := by
  intro Z W h
  apply injective_integralClosedSubspaceSupport B S hS (isAlgebraicSpace_yoneda B S hS U)
  apply IrreducibleCloseds.ext
  show subspacePointSet B S hS (yoneda.obj U) Z.subspace =
    subspacePointSet B S hS (yoneda.obj U) W.subspace
  apply (Set.image_injective.2 (injective_pointsToScheme B S hS U))
  rw [Z.image_subspacePointSet B S hS U, W.image_subspacePointSet B S hS U, h]

/-- Every point of `U` is the generic point of an integral closed subspace of `h_U`, namely of
the reduced closed subspace on the closure of the corresponding point, Stacks 0ENF. -/
theorem IntegralClosedSubspace.surjective_schemeGenericPoint :
    Function.Surjective (IntegralClosedSubspace.schemeGenericPoint B S hS U) := by
  intro x
  set p := (pointsEquivScheme B S hS U).symm x
  obtain ⟨Z, hZ⟩ := surjective_integralClosedSubspaceSupport B S hS
    (isAlgebraicSpace_yoneda B S hS U) (isDecentSpace_yoneda B S hS U)
    (IrreducibleCloseds.closureSingleton p)
  refine ⟨Z, ?_⟩
  have hgen : IsGenericPoint p (subspacePointSet B S hS (yoneda.obj U) Z.subspace) :=
    isGenericPoint_def.2 (congrArg (fun T : IrreducibleCloseds (points B S hS (yoneda.obj U)) =>
      (T : Set (points B S hS (yoneda.obj U)))) hZ).symm
  have hp := eq_pointsMap_genericPoint_of_isGenericPoint B S hS
    (isAlgebraicSpace_yoneda B S hS U) Z p hgen
  rw [schemeGenericPoint, ← hp]
  exact (pointsEquivScheme B S hS U).apply_symm_apply x

/-- Every point of `U` is the generic point of exactly one integral closed subspace of `h_U`. -/
theorem IntegralClosedSubspace.bijective_schemeGenericPoint :
    Function.Bijective (IntegralClosedSubspace.schemeGenericPoint B S hS U) :=
  ⟨IntegralClosedSubspace.injective_schemeGenericPoint B S hS U,
    IntegralClosedSubspace.surjective_schemeGenericPoint B S hS U⟩

/-- The bijection between the integral closed subspaces of the algebraic space `h_U` and the
points of the scheme `U`, sending an integral closed subspace to its generic point. A point
`x` of `U` stands for the integral closed subscheme `closure {x}` of `U`, so this is the
bijection between integral closed subspaces of `h_U` and integral closed subschemes of `U`. -/
def IntegralClosedSubspace.equivSchemePoints :
    IntegralClosedSubspace B S hS (yoneda.obj U) ≃ (BigFppfOver.toScheme B S hS).obj U :=
  Equiv.ofBijective _ (IntegralClosedSubspace.bijective_schemeGenericPoint B S hS U)

/-- The bijection `equivSchemePoints` sends an integral closed subspace of `h_U` to its generic
point in `U`. -/
@[simp]
theorem IntegralClosedSubspace.equivSchemePoints_apply
    (Z : IntegralClosedSubspace B S hS (yoneda.obj U)) :
    IntegralClosedSubspace.equivSchemePoints B S hS U Z = Z.schemeGenericPoint B S hS U :=
  rfl

/-- The generic point of the integral closed subspace of `h_U` corresponding to a point `x` of `U`
is `x`. -/
@[simp]
theorem IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ((IntegralClosedSubspace.equivSchemePoints B S hS U).symm x).schemeGenericPoint B S hS U =
      x :=
  (IntegralClosedSubspace.equivSchemePoints B S hS U).apply_symm_apply x

/-- The set of points, read in `U`, of the integral closed subspace of `h_U` corresponding to a
point `x` of `U` is the closure of `x`. -/
theorem IntegralClosedSubspace.image_subspacePointSet_equivSchemePoints_symm
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    pointsToScheme B S hS U '' subspacePointSet B S hS (yoneda.obj U)
        ((IntegralClosedSubspace.equivSchemePoints B S hS U).symm x).subspace =
      closure {x} := by
  rw [IntegralClosedSubspace.image_subspacePointSet,
    IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]

end Points

/-! ### Local finiteness -/

section LocallyFinite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- **The local finiteness conditions of Stacks 0EDZ and Stacks 02QR agree on a represented
space.** A family of coefficients on the integral closed subspaces of `h_U` is locally finite in
the sense of Stacks 0EDZ — the point sets of the subspaces with nonzero coefficient form a
locally finite family in `|h_U|` — exactly when the corresponding function on the points of `U`
has locally finite support. -/
theorem locallyFinite_iff_locallyFiniteSupport
    (α : IntegralClosedSubspace B S hS (yoneda.obj U) → ℤ) :
    (LocallyFinite fun Z : IntegralClosedSubspace B S hS (yoneda.obj U) =>
        if α Z = 0 then ∅ else subspacePointSet B S hS (yoneda.obj U) Z.subspace) ↔
      LocallyFiniteSupport fun x : (BigFppfOver.toScheme B S hS).obj U =>
        α ((IntegralClosedSubspace.equivSchemePoints B S hS U).symm x) := by
  set e := IntegralClosedSubspace.equivSchemePoints B S hS U
  set h := schemePointsHomeomorph B S hS U
  constructor
  · intro hfin z
    obtain ⟨t, ht, hI⟩ := hfin (h.symm z)
    refine ⟨h '' t, ?_, (hI.image e).subset ?_⟩
    · have := h.isOpenMap.image_mem_nhds ht
      rwa [h.apply_symm_apply] at this
    · rintro x ⟨⟨q, hqt, rfl⟩, hx⟩
      have hx' : α (e.symm (h q)) ≠ 0 := hx
      refine ⟨e.symm (h q), ⟨q, ?_, hqt⟩, e.apply_symm_apply _⟩
      show q ∈ (if α (e.symm (h q)) = 0 then ∅ else
        subspacePointSet B S hS (yoneda.obj U) (e.symm (h q)).subspace)
      rw [if_neg hx', IntegralClosedSubspace.mem_subspacePointSet_iff,
        IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]
      exact subset_closure rfl
  · intro hβ p
    obtain ⟨t, ht, hfin⟩ := hβ (h p)
    refine ⟨h ⁻¹' interior t, h.continuous.continuousAt.preimage_mem_nhds
      (interior_mem_nhds.2 ht), (hfin.image e.symm).subset ?_⟩
    rintro Z ⟨q, hqZ, hqt⟩
    change q ∈ (if α Z = 0 then ∅ else subspacePointSet B S hS (yoneda.obj U) Z.subspace) at hqZ
    have hZ : α Z ≠ 0 := fun h0 => by rwa [if_pos h0] at hqZ
    rw [if_neg hZ, IntegralClosedSubspace.mem_subspacePointSet_iff] at hqZ
    have hgen : Z.schemeGenericPoint B S hS U ∈ interior t :=
      (specializes_iff_mem_closure.2 hqZ).mem_open isOpen_interior hqt
    refine ⟨Z.schemeGenericPoint B S hS U, ⟨interior_subset hgen, ?_⟩, e.symm_apply_apply Z⟩
    show α (e.symm (e Z)) ≠ 0
    rwa [e.symm_apply_apply]

end LocallyFinite

/-! ### Compatible dimension functions -/

section Delta

variable (D : BaseSpaceDimensionSituation.{u}) (U : BigFppfOver D.site D.base D.base_mem)
    (sX : yoneda.obj U ⟶ D.space) (C : Stacks.Chow.ChowSituation.{u})
    (s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S)

/-- The scheme situation `(C.S, δ)` with the morphism `s₀ : U → C.S` is *δ-compatible* with the
good space `h_U → B` of Situation 0EDT when the dimension function `δ_{U/C.S}` of Stacks 02JW
agrees with `δ_{h_U/B}` of Stacks 0EDT at every point, the points of `h_U` and of `U` being
identified as in Stacks 03BX. -/
def IsDeltaCompatible : Prop :=
  ∀ x : points D.site D.base D.base_mem (yoneda.obj U),
    Stacks.Chow.relativeDimension C.dimensionFunction s₀
      (pointsToScheme D.site D.base D.base_mem U x) = D.deltaValue sX x

variable {D U sX C s₀}

/-- Under a δ-compatible scheme situation, the dimension function of `h_U` at the point
corresponding to a point `x` of `U` is the relative dimension function of `U` at `x`. -/
theorem IsDeltaCompatible.deltaValue_symm (h : IsDeltaCompatible D U sX C s₀)
    (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U) :
    D.deltaValue sX ((pointsEquivScheme D.site D.base D.base_mem U).symm x) =
      Stacks.Chow.relativeDimension C.dimensionFunction s₀ x := by
  rw [← h]
  exact congrArg _ ((pointsEquivScheme D.site D.base D.base_mem U).apply_symm_apply x)

/-- Under a δ-compatible scheme situation, the δ-dimension of an integral closed subspace of
`h_U` is the relative dimension function of `U` at its generic point. -/
theorem IsDeltaCompatible.deltaDimension_eq (h : IsDeltaCompatible D U sX C s₀)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U)) :
    deltaDimension D sX Z =
      Stacks.Chow.relativeDimension C.dimensionFunction s₀
        (Z.schemeGenericPoint D.site D.base D.base_mem U) :=
  (h _).symm

/-- **The bijection of integral closed subspaces preserves δ-dimension.** Under a δ-compatible
scheme situation, the δ-dimension of an integral closed subspace `Z` of `h_U`, Stacks 0EDX, is
the δ-dimension, Stacks 02QP, of the corresponding integral closed subscheme of `U`, the closure
of the generic point of `Z`. -/
theorem deltaDimension_eq_schemeDeltaDimension [LocallyOfFiniteType s₀]
    (h : IsDeltaCompatible D U sX C s₀)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U)) :
    deltaDimension D sX Z =
      Stacks.Chow.deltaDimension C s₀
        ⟨closure {Z.schemeGenericPoint D.site D.base D.base_mem U},
          isIrreducible_singleton.closure, isClosed_closure⟩ := by
  rw [Stacks.Chow.deltaDimension_closure_singleton, h.deltaDimension_eq]

end Delta

/-! ### The cycle groups -/

section CycleGroup

variable {D : BaseSpaceDimensionSituation.{u}} {U : BigFppfOver D.site D.base D.base_mem}
    {sX : yoneda.obj U ⟶ D.space} {C : Stacks.Chow.ChowSituation.{u}}
    {s₀ : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U ⟶ C.S} [LocallyOfFiniteType s₀]

/-- The function on the points of `U` corresponding to a family of coefficients on the integral
closed subspaces of `h_U`, for a family whose corresponding function has locally finite
support. -/
def schemeCycleOfLocallyFiniteSupport
    (α : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U) → ℤ)
    (hα : LocallyFiniteSupport fun x =>
      α ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x)) :
    AlgebraicCycle ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U) ℤ :=
  ⟨fun x => α ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x),
    by simp, fun z _ => hα z⟩

/-- A cycle on `U`, read on the integral closed subspaces of `h_U` through their generic points,
is a family whose corresponding function is the cycle itself. -/
theorem algebraicCycle_comp_schemeGenericPoint
    (c : AlgebraicCycle ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U) ℤ) :
    (fun x => c (((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
      x).schemeGenericPoint D.site D.base D.base_mem U)) = ⇑c :=
  funext fun x => congrArg c
    (IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm _ _ _ U x)

/-- A family of coefficients on the integral closed subspaces of `h_U` is a `k`-cycle, Stacks
0EDZ, exactly when the corresponding function on the points of `U` has locally finite support
and is a `k`-cycle, Stacks 02QR. -/
theorem mem_cyclesOfDimension_iff_mem_scheme (h : IsDeltaCompatible D U sX C s₀) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U) → ℤ) :
    α ∈ cyclesOfDimension D sX k ↔
      ∃ hα : LocallyFiniteSupport fun x =>
          α ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x),
        schemeCycleOfLocallyFiniteSupport α hα ∈ Stacks.Chow.cyclesOfDimension C s₀ k := by
  set e := IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U
  rw [mem_cyclesOfDimension_iff, locallyFinite_iff_locallyFiniteSupport]
  refine ⟨fun ⟨hα, hdim⟩ => ⟨hα, ?_⟩, fun ⟨hα, hdim⟩ => ⟨hα, ?_⟩⟩
  · rw [Stacks.Chow.mem_cyclesOfDimension_iff_forall_point]
    intro x hx
    have := hdim (e.symm x) hx
    rwa [h.deltaDimension_eq, IntegralClosedSubspace.schemeGenericPoint_equivSchemePoints_symm]
      at this
  · rw [Stacks.Chow.mem_cyclesOfDimension_iff_forall_point] at hdim
    intro Z hZ
    have := hdim (e Z) (by
      show α (e.symm (e Z)) ≠ 0
      rwa [e.symm_apply_apply])
    rwa [h.deltaDimension_eq]

variable (sX s₀) in
/-- **`Z_k(h_U) ≅ Z_k(U)`.** Under a δ-compatible scheme situation, the group of `k`-cycles on
the represented algebraic space `h_U`, Stacks 0EDZ, is isomorphic to the group of `k`-cycles on
the scheme `U`, Stacks 02QR: the cycle `∑ n_Z [Z]` goes to the cycle with the coefficient `n_Z`
at the generic point of `Z`. -/
def cycleGroupEquivScheme (h : IsDeltaCompatible D U sX C s₀) (k : ℤ) :
    CycleGroup D sX k ≃+ Stacks.Chow.CycleGroup C s₀ k where
  toFun α :=
    ⟨schemeCycleOfLocallyFiniteSupport α.1
      ((mem_cyclesOfDimension_iff_mem_scheme h k α.1).1 α.2).1,
      ((mem_cyclesOfDimension_iff_mem_scheme h k α.1).1 α.2).2⟩
  invFun c :=
    ⟨fun Z => c.1 (Z.schemeGenericPoint D.site D.base D.base_mem U), by
      have hc : LocallyFiniteSupport fun x => c.1
          (((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
            x).schemeGenericPoint D.site D.base D.base_mem U) := by
        rw [algebraicCycle_comp_schemeGenericPoint]
        exact c.1.locallyFiniteSupport
      refine (mem_cyclesOfDimension_iff_mem_scheme h k
        (fun Z => c.1 (Z.schemeGenericPoint D.site D.base D.base_mem U))).2 ⟨hc, ?_⟩
      have heq : schemeCycleOfLocallyFiniteSupport
          (fun Z => c.1 (Z.schemeGenericPoint D.site D.base D.base_mem U)) hc = c.1 :=
        Function.locallyFinsuppWithin.ext fun x =>
          congrFun (algebraicCycle_comp_schemeGenericPoint c.1) x
      rw [heq]
      exact c.2⟩
  left_inv α := by
    apply Subtype.ext
    funext Z
    change α.1 ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm
      (IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U Z)) = α.1 Z
    rw [Equiv.symm_apply_apply]
  right_inv c :=
    Subtype.ext (Function.locallyFinsuppWithin.ext fun x =>
      congrFun (algebraicCycle_comp_schemeGenericPoint c.1) x)
  map_add' _ _ := rfl

/-- The coefficient of the image of a cycle at a point of `U` is the coefficient of the cycle
at the corresponding integral closed subspace of `h_U`. -/
@[simp]
theorem cycleGroupEquivScheme_apply (h : IsDeltaCompatible D U sX C s₀) (k : ℤ)
    (α : CycleGroup D sX k) (x : (BigFppfOver.toScheme D.site D.base D.base_mem).obj U) :
    (cycleGroupEquivScheme sX s₀ h k α).1 x =
      α.1 ((IntegralClosedSubspace.equivSchemePoints D.site D.base D.base_mem U).symm x) :=
  rfl

/-- The coefficient of the inverse image of a cycle on `U` at an integral closed subspace of
`h_U` is its coefficient at the generic point of that subspace. -/
@[simp]
theorem cycleGroupEquivScheme_symm_apply (h : IsDeltaCompatible D U sX C s₀) (k : ℤ)
    (c : Stacks.Chow.CycleGroup C s₀ k)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem (yoneda.obj U)) :
    ((cycleGroupEquivScheme sX s₀ h k).symm c).1 Z =
      c.1 (Z.schemeGenericPoint D.site D.base D.base_mem U) :=
  rfl

end CycleGroup

end AlgebraicGeometry.Space

end
