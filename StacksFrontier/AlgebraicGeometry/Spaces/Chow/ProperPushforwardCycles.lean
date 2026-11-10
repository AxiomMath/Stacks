module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Cycles
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EqualDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle

/-!
# Proper pushforward of cycles on good algebraic spaces

In the situation of [Stacks, Tag 0EDT] let `X/B` and `Y/B` be good and let `f : X ⟶ Y` be a
quasi-compact morphism over `B`. This module constructs the pushforward `f_* : Z_k(X) → Z_k(Y)`
of cycles of [Stacks, Tag 0EP1].

On a prime cycle `[Z]` it is

  `f_*[Z] = deg(Z/Z') · [Z']` when `dim_δ(Z') = dim_δ(Z)`, and `f_*[Z] = 0` when `dim_δ` drops,

where `Z'` is the integral closed subspace of `Y` on the closure of the image of `|Z|` and
`deg(Z/Z') = [R(Z) : R(Z')]`. The degree is taken between the residue fields of the ambient spaces
at the generic points of `Z` and of `Z'`, which are the function fields `R(Z)` and `R(Z')`
([Stacks, Tag 0ENX]). It is `Module.finrank`, hence `0` on an extension which is not finite.

## Main definitions

* `AlgebraicGeometry.Space.functionFieldDegree`: the degree `[R(Z) : R(Z')]` of the extension of
  function fields induced by `f` at the generic point of an integral closed subspace `Z ⊆ X`.
* `AlgebraicGeometry.Space.properCycleDegree`: that degree cut down to `0` where the δ-dimension
  drops, which is the coefficient of `[Z']` in `f_*[Z]`.
* `AlgebraicGeometry.Space.properCycleMult`: the multiplicity of an arbitrary integral closed
  subspace of `Y` in `f_*[Z]`.
* `AlgebraicGeometry.Space.cycleSupportFamily`: the family of point sets whose local finiteness
  is the cycle condition of [Stacks, Tag 0EDZ].
* `AlgebraicGeometry.Space.properCyclePushforwardCoeff`: the coefficient family of `f_*α`.
* `AlgebraicGeometry.Space.properCyclePushforward`: the pushforward of cycles, as an additive map
  `Z_k(X) →+ Z_k(Y)`.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.ambientGenericPoint_closureImage_eq`: `f` carries
  the generic point of `Z` to the generic point of the integral closed subspace of `Y` on the
  closure of the image of `|Z|`.
* `AlgebraicGeometry.Space.finite_properCycleFibre`: for a cycle `α` on `X` and an integral
  closed subspace `Z' ⊆ Y`, only finitely many integral closed subspaces in the support of `α`
  have `Z'` for the closure of their image.
* `AlgebraicGeometry.Space.properCyclePushforwardCoeff_mem_cyclesOfDimension`: the pushforward of a
  `k`-cycle is a `k`-cycle.
* `AlgebraicGeometry.Space.properPushforward_apply`: the coefficient of `f_*α` at `Z'` is the
  defining sum `∑ α_Z · deg(Z/Z')`.
* `AlgebraicGeometry.Space.deltaDimension_closureImage_of_properCycleDegree_ne_zero`: a nonzero
  degree forces the δ-dimension to be preserved.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0ENX](https://stacks.math.columbia.edu/tag/0ENX)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The generic point of the closure of the image -/

section GenericPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The closure of the image of the point set of an integral closed subspace `Z ⊆ X` under a
morphism `f : X ⟶ Y` is the closure of the image of the generic point of `Z`. -/
theorem IntegralClosedSubspace.closure_image_subspacePointSet (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) (Z : IntegralClosedSubspace B S hS X) :
    closure (pointsMap B S hS X f '' subspacePointSet B S hS X Z.subspace) =
      closure ({pointsMap B S hS X f (Z.ambientGenericPoint B S hS)} :
        Set (points B S hS Y)) := by
  have hgen := Z.isGenericPoint_ambientGenericPoint B S hS hX
  refine subset_antisymm ?_ ?_
  · refine closure_minimal ?_ isClosed_closure
    rw [← hgen]
    refine (image_closure_subset_closure_image (continuous_pointsMap B S hS f)).trans ?_
    rw [Set.image_singleton]
  · refine closure_mono ?_
    rw [Set.singleton_subset_iff]
    exact Set.mem_image_of_mem _ (by rw [← hgen]; exact subset_closure rfl)

/-- A morphism carries the generic point of an integral closed subspace `Z ⊆ X` to the generic
point of the integral closed subspace of `Y` on the closure of the image of `|Z|`. -/
theorem IntegralClosedSubspace.ambientGenericPoint_closureImage_eq (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hYdec : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS X) :
    (IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).ambientGenericPoint B S hS =
      pointsMap B S hS X f (Z.ambientGenericPoint B S hS) := by
  have ht0 : T0Space (points B S hS Y) := t0Space_points_of_isDecentSpace B S hS hY hYdec
  refine IsGenericPoint.eq
    ((IntegralClosedSubspace.closureImage B S hS hY hYdec f Z).isGenericPoint_ambientGenericPoint
      B S hS hY) ?_
  rw [IntegralClosedSubspace.subspacePointSet_closureImage B S hS hY hYdec f Z]
  exact (IntegralClosedSubspace.closure_image_subspacePointSet B S hS hX f Z).symm

end GenericPoint

/-! ### The degree of the extension of function fields -/

section Degree

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The degree of the extension of function fields induced by a morphism `f : X ⟶ Y` of good
algebraic spaces at the generic point of an integral closed subspace `Z ⊆ X`: the degree
`[R(Z) : R(Z')]` of the residue field of `X` at that point over the residue field of `Y` at its
image, as `Module.finrank`, hence `0` when the extension is not finite. -/
noncomputable def functionFieldDegree (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℕ :=
  letI := (residueFieldHom D.site D.base D.base_mem X Y hY.1
    (D.isDecentSpace_of_isGood sX hX) (D.isDecentSpace_of_isGood sY hY) f
    (Z.ambientGenericPoint D.site D.base D.base_mem)).toAlgebra
  Module.finrank
    (residueField D.site D.base D.base_mem Y (D.isDecentSpace_of_isGood sY hY)
      (pointsMap D.site D.base D.base_mem X f
        (Z.ambientGenericPoint D.site D.base D.base_mem)))
    (residueField D.site D.base D.base_mem X (D.isDecentSpace_of_isGood sX hX)
      (Z.ambientGenericPoint D.site D.base D.base_mem))

/-- The coefficient with which the closure `Z'` of the image of an
integral closed subspace `Z ⊆ X` occurs in `f_*[Z]`: the degree `[R(Z) : R(Z')]` when the
δ-dimension is preserved, and `0` when it drops. -/
@[stacks 0EP1 "part (1): the coefficient of the image in the pushforward of a prime cycle"]
noncomputable def properCycleDegree (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) : ℤ :=
  if deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z) = deltaDimension D sX Z then
    (functionFieldDegree D sX hX sY hY f Z : ℤ)
  else 0

/-- The δ-dimension is preserved whenever `properCycleDegree` is nonzero. -/
theorem deltaDimension_closureImage_of_properCycleDegree_ne_zero (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X}
    (hZ : properCycleDegree D sX hX sY hY f Z ≠ 0) :
    deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z) = deltaDimension D sX Z := by
  by_contra hne
  refine hZ ?_
  change (if deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) f Z) = deltaDimension D sX Z then
    ((functionFieldDegree D sX hX sY hY f Z : ℤ)) else 0) = 0
  split_ifs
  rfl

open scoped Classical in
/-- The multiplicity with which an integral closed subspace `Z' ⊆ Y` occurs in `f_*[Z]`:
`properCycleDegree` when `Z'` is the closure of the image of `|Z|`, and `0` otherwise. -/
noncomputable def properCycleMult (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) : ℤ :=
  if IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z = Z' then
    properCycleDegree D sX hX sY hY f Z
  else 0

/-- A nonzero multiplicity forces the subspace to be the closure of the image and the degree to
be nonzero; conversely those two conditions give a nonzero multiplicity. -/
theorem properCycleMult_ne_zero_iff (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    properCycleMult D sX hX sY hY f Z Z' ≠ 0 ↔
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z = Z' ∧
        properCycleDegree D sX hX sY hY f Z ≠ 0 := by
  unfold properCycleMult
  split_ifs with h
  · exact (and_iff_right h).symm
  · exact ⟨fun hc => absurd rfl hc, fun hc => absurd hc.1 h⟩

/-- An integral closed subspace which is not the closure of the image of `|Z|` has multiplicity
zero in `f_*[Z]`. -/
theorem properCycleMult_eq_zero_of_ne (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hZ' : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z ≠ Z') :
    properCycleMult D sX hX sY hY f Z Z' = 0 := by
  by_contra hc
  exact hZ' ((properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 hc).1

end Degree

/-! ### Finiteness of the family contributing to one integral closed subspace -/

section Fibre

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The point sets of the integral closed subspaces with a nonzero coefficient: the family whose
local finiteness is the cycle condition on `α`. -/
abbrev cycleSupportFamily (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Set (points D.site D.base D.base_mem X) :=
  if α Z = 0 then ∅ else subspacePointSet D.site D.base D.base_mem X Z.subspace

/-- At a subspace with nonzero coefficient the support family is the point set of that
subspace. -/
theorem cycleSupportFamily_of_ne_zero
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (hZ : α Z ≠ 0) :
    cycleSupportFamily D α Z = subspacePointSet D.site D.base D.base_mem X Z.subspace := by
  unfold cycleSupportFamily
  split_ifs with h
  · exact absurd h hZ
  · rfl

/-- Each member of the support family is closed. -/
theorem isClosed_cycleSupportFamily (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X) :
    IsClosed (cycleSupportFamily D α Z) := by
  unfold cycleSupportFamily
  split_ifs with h
  · exact isClosed_empty
  · exact isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 Z

/-- The point set of the integral closed subspace of `Y` on the closure of the image of a
subspace with nonzero coefficient is the closure of the image of the support family there. -/
theorem closure_image_cycleSupportFamily (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X} (hZ : α Z ≠ 0) :
    closure (pointsMap D.site D.base D.base_mem X f '' cycleSupportFamily D α Z) =
      subspacePointSet D.site D.base D.base_mem Y
        (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z).subspace := by
  rw [cycleSupportFamily_of_ne_zero D α hZ,
    IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f Z]

/-- For a cycle `α` on `X`, a quasi-compact `f`, and an integral closed subspace `Z' ⊆ Y`, only
finitely many integral closed subspaces in the support of `α` have `Z'` for the closure of their
image. -/
theorem finite_properCycleFibre (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : LocallyFinite (cycleSupportFamily D α))
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    {Z : IntegralClosedSubspace D.site D.base D.base_mem X | α Z ≠ 0 ∧
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z = Z'}.Finite := by
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf
    (cycleSupportFamily D α) (isClosed_cycleSupportFamily D sX hX α) hα
  obtain ⟨V, hV, hVfin⟩ := hlf (Z'.ambientGenericPoint D.site D.base D.base_mem)
  refine hVfin.subset ?_
  rintro Z ⟨hZne, hZim⟩
  refine ⟨Z'.ambientGenericPoint D.site D.base D.base_mem, ?_, mem_of_mem_nhds hV⟩
  change Z'.ambientGenericPoint D.site D.base D.base_mem ∈
    closure (pointsMap D.site D.base D.base_mem X f '' cycleSupportFamily D α Z)
  rw [closure_image_cycleSupportFamily D sY hY f α hZne, hZim,
    ← Z'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1]
  exact subset_closure rfl

end Fibre

/-! ### The proper pushforward of cycles -/

section Pushforward

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The coefficient of the pushforward `f_*α` at an integral closed
subspace `Z' ⊆ Y`: the sum of `α_Z` times the multiplicity of `Z'` in `f_*[Z]`. -/
noncomputable def properCyclePushforwardCoeff (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) : ℤ :=
  ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
    α Z * properCycleMult D sX hX sY hY f Z Z'

/-- The summands of the defining sum are supported on the subspaces of the support of `α` whose
image closure is `Z'`. -/
theorem support_subset_properCycleFibre (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (Function.support fun Z => α Z * properCycleMult D sX hX sY hY f Z Z') ⊆
      {Z | α Z ≠ 0 ∧ IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f Z = Z'} := by
  intro Z hZ
  have hne : α Z * properCycleMult D sX hX sY hY f Z Z' ≠ 0 := hZ
  exact ⟨left_ne_zero_of_mul hne,
    ((properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 (right_ne_zero_of_mul hne)).1⟩

/-- For a quasi-compact `f` and a cycle `α`, the summands of `properCyclePushforwardCoeff` have
finite support. -/
theorem hasFiniteSupport_properCycleMult (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : LocallyFinite (cycleSupportFamily D α))
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    Function.HasFiniteSupport fun Z => α Z * properCycleMult D sX hX sY hY f Z Z' :=
  (finite_properCycleFibre D sX hX sY hY hfB hf α hα Z').subset
    (support_subset_properCycleFibre D sX hX sY hY f α Z')

/-- A nonzero coefficient of the pushforward comes from an integral closed subspace in the
support of `α` whose image closure is `Z'` and whose degree is nonzero. -/
theorem exists_of_properPushforwardCoeff_ne_zero (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hZ' : properCyclePushforwardCoeff D sX hX sY hY f α Z' ≠ 0) :
    ∃ Z : IntegralClosedSubspace D.site D.base D.base_mem X, α Z ≠ 0 ∧
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z = Z' ∧
        properCycleDegree D sX hX sY hY f Z ≠ 0 := by
  by_contra hcon
  refine hZ' (finsum_eq_zero_of_forall_eq_zero fun Z => ?_)
  by_cases hα : α Z = 0
  · rw [hα, zero_mul]
  · by_cases hmult : properCycleMult D sX hX sY hY f Z Z' = 0
    · rw [hmult, mul_zero]
    · obtain ⟨him, hdeg⟩ := (properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 hmult
      exact absurd ⟨Z, hα, him, hdeg⟩ hcon

/-- The pushforward of a `k`-cycle is a `k`-cycle: its support is locally finite, and every
integral closed subspace carrying a nonzero coefficient has δ-dimension `k`. -/
theorem properCyclePushforwardCoeff_mem_cyclesOfDimension (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ) (α : CycleGroup D sX k) :
    properCyclePushforwardCoeff D sX hX sY hY f α.1 ∈ cyclesOfDimension D sY k := by
  obtain ⟨hαfin, hαdim⟩ := α.2
  obtain ⟨hlf, -⟩ := locallyFinite_closure_image_pointsMap D sX hX sY hY hfB hf
    (cycleSupportFamily D α.1) (isClosed_cycleSupportFamily D sX hX α.1) hαfin
  refine ⟨fun x => ?_, fun Z' hZ' => ?_⟩
  · obtain ⟨V, hV, hVfin⟩ := hlf x
    refine ⟨V, hV, (hVfin.image (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) f)).subset ?_⟩
    rintro Z' ⟨p, hp, hpV⟩
    have hp' : p ∈ (if properCyclePushforwardCoeff D sX hX sY hY f α.1 Z' = 0 then
        (∅ : Set (points D.site D.base D.base_mem Y))
      else subspacePointSet D.site D.base D.base_mem Y Z'.subspace) := hp
    split_ifs at hp' with hcoeff
    · exact absurd hp' (Set.notMem_empty p)
    obtain ⟨Z, hZne, hZim, -⟩ :=
      exists_of_properPushforwardCoeff_ne_zero D sX hX sY hY f α.1 hcoeff
    refine ⟨Z, ⟨p, ?_, hpV⟩, hZim⟩
    change p ∈ closure (pointsMap D.site D.base D.base_mem X f '' cycleSupportFamily D α.1 Z)
    rw [closure_image_cycleSupportFamily D sY hY f α.1 hZne, hZim]
    exact hp'
  · obtain ⟨Z, hZne, hZim, hdeg⟩ :=
      exists_of_properPushforwardCoeff_ne_zero D sX hX sY hY f α.1 hZ'
    rw [← hZim, deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY f hdeg]
    exact hαdim Z hZne

/-- The proper pushforward of cycles along a quasi-compact morphism `f : X ⟶ Y` of good
algebraic spaces over `B`: the additive map `f_* : Z_k(X) → Z_k(Y)` sending a cycle `α` to the
cycle whose coefficient at `Z'` is `∑ α_Z · [R(Z) : R(Z')]`, the sum being over the integral
closed subspaces `Z ⊆ X` whose image closure is `Z'` and the degree being taken to be `0` where
the δ-dimension drops. The morphism `f` is assumed quasi-compact, not proper. -/
@[stacks 0EP1 "part (2): the pushforward of a k-cycle, as a homomorphism of abelian groups"]
noncomputable def properCyclePushforward (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ) :
    CycleGroup D sX k →+ CycleGroup D sY k where
  toFun α := ⟨properCyclePushforwardCoeff D sX hX sY hY f α.1,
    properCyclePushforwardCoeff_mem_cyclesOfDimension D sX hX sY hY hfB hf k α⟩
  map_zero' := by
    refine Subtype.ext (funext fun Z' => ?_)
    change properCyclePushforwardCoeff D sX hX sY hY f (0 : CycleGroup D sX k).1 Z' = 0
    exact finsum_eq_zero_of_forall_eq_zero fun Z => by
      change (0 : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ) Z * _ = 0
      rw [Pi.zero_apply, zero_mul]
  map_add' := by
    intro α β
    refine Subtype.ext (funext fun Z' => ?_)
    change properCyclePushforwardCoeff D sX hX sY hY f (α.1 + β.1) Z' =
      properCyclePushforwardCoeff D sX hX sY hY f α.1 Z' +
        properCyclePushforwardCoeff D sX hX sY hY f β.1 Z'
    rw [properCyclePushforwardCoeff, properCyclePushforwardCoeff, properCyclePushforwardCoeff,
      ← finsum_add_distrib (hasFiniteSupport_properCycleMult D sX hX sY hY hfB hf α.1 α.2.1 Z')
        (hasFiniteSupport_properCycleMult D sX hX sY hY hfB hf β.1 β.2.1 Z')]
    exact finsum_congr fun Z => by rw [Pi.add_apply, add_mul]

/-- The coefficient of the proper pushforward at an integral
closed subspace `Z' ⊆ Y` is the defining sum. -/
theorem properPushforward_apply (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space)
    (hY : D.IsGood sY) {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f) (k : ℤ) (α : CycleGroup D sX k)
    (Z' : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    (properCyclePushforward D sX hX sY hY hfB hf k α).1 Z' =
      ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 Z * properCycleMult D sX hX sY hY f Z Z' :=
  rfl

end Pushforward

end AlgebraicGeometry.Space

end
