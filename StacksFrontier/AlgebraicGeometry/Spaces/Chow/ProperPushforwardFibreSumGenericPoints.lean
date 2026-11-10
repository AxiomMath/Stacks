module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardFibreSum

/-!
# The pushforward coefficient of an arbitrary cycle, as a sum over a fibre

For a morphism `f : X ⟶ Y` of algebraic spaces and a coefficient family `α` on the integral
closed subspaces of `X` supported in δ-dimension `k`, the defining sum of the coefficient of the
proper pushforward of `α` at an integral closed subspace `W ⊂ Y` of δ-dimension `k` is a sum over
the points of `|X|` above the generic point of `W`.

## Main results

* `IntegralClosedSubspace.integralClosedSubspaceOfPoint_ambientGenericPoint`: an integral closed
  subspace is the one attached to its own ambient generic point.
* `IntegralClosedSubspace.injective_ambientGenericPoint`: an integral closed subspace of a decent
  algebraic space is determined by its ambient generic point.
* `bijOn_ambientGenericPoint_cycleSupport_fibre`: the support of a coefficient family over `W`,
  indexed by points of the fibre.
* `finsum_mul_properCycleMult_eq_finsum_fibre`: the pushforward coefficient of an arbitrary cycle
  as a sum over the fibre.

## References

* [Stacks Project, Tag 0EDV](https://stacks.math.columbia.edu/tag/0EDV)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

/-! ### The pushforward coefficient of an arbitrary cycle, as a sum over a fibre -/

section OfPoint

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An integral closed subspace is the one attached to its own ambient generic point.** -/
theorem IntegralClosedSubspace.integralClosedSubspaceOfPoint_ambientGenericPoint
    (hX : IsAlgebraicSpace B S hS X) (hdec : IsDecentSpace B S hS X)
    (Z : IntegralClosedSubspace B S hS X) :
    integralClosedSubspaceOfPoint B S hS hX hdec (Z.ambientGenericPoint B S hS) = Z :=
  (eq_integralClosedSubspaceOfPoint B S hS hX hdec _ Z
    (Z.isGenericPoint_ambientGenericPoint B S hS hX)).symm

/-- **An integral closed subspace of a decent algebraic space is determined by its ambient
generic point.** -/
theorem IntegralClosedSubspace.injective_ambientGenericPoint (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) :
    Function.Injective fun Z : IntegralClosedSubspace B S hS X =>
      Z.ambientGenericPoint B S hS :=
  Function.LeftInverse.injective (integralClosedSubspaceOfPoint_ambientGenericPoint B S hS hX hdec)

end OfPoint

include hY in
/-- **The fibre of the support of a coefficient family, indexed by integral closed subspaces.**
Taking ambient generic points is a bijection from the integral closed subspaces `Z ⊂ X` with
`α Z ≠ 0` and image closure `W` onto the points `x` over the generic point of `W` whose
attached integral closed subspace has `α ≠ 0`. -/
theorem bijOn_ambientGenericPoint_cycleSupport_fibre (f : X ⟶ Y)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    Set.BijOn (fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
        Z.ambientGenericPoint D.site D.base D.base_mem)
      {Z | α Z ≠ 0 ∧
        IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z = W}
      {x | pointsMap D.site D.base D.base_mem X f x =
          W.ambientGenericPoint D.site D.base D.base_mem ∧
        α (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
          (D.isDecentSpace_of_isGood sX hX) x) ≠ 0} := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hofpt : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec
        (Z.ambientGenericPoint D.site D.base D.base_mem) = Z :=
    IntegralClosedSubspace.integralClosedSubspaceOfPoint_ambientGenericPoint D.site D.base
      D.base_mem hX.1 hXdec
  have himg : ∀ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
      IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z = W ↔
        pointsMap D.site D.base D.base_mem X f
            (Z.ambientGenericPoint D.site D.base D.base_mem) =
          W.ambientGenericPoint D.site D.base D.base_mem := by
    intro Z
    constructor
    · intro h
      rw [← IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
        hX.1 hY.1 hYdec f Z, h]
    · intro h
      refine IntegralClosedSubspace.injective_ambientGenericPoint D.site D.base D.base_mem hY.1
        hYdec ?_
      change (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f
        Z).ambientGenericPoint D.site D.base D.base_mem = _
      rw [IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
        hX.1 hY.1 hYdec f Z, h]
  have hagp : ∀ x : points D.site D.base D.base_mem X,
      (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec
        x).ambientGenericPoint D.site D.base D.base_mem = x :=
    pointsMap_genericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec
  refine ⟨fun Z hZ => ⟨(himg Z).1 hZ.2, ?_⟩,
    fun Z₁ _ Z₂ _ h =>
      IntegralClosedSubspace.injective_ambientGenericPoint D.site D.base D.base_mem hX.1 hXdec h,
    fun x hx => ⟨integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x,
      ⟨hx.2, ?_⟩, hagp x⟩⟩
  · rw [hofpt Z]
    exact hZ.1
  · rw [himg, hagp x]
    exact hx.1

include hY in
/-- **The pushforward coefficient of an arbitrary cycle as a sum over the fibre.** Let `α` be a
coefficient family on the integral closed subspaces of `X` supported in δ-dimension `k`, and let
`W ⊂ Y` be an integral closed subspace of δ-dimension `k` with generic point `η`. Then the
defining sum of the pushforward coefficient of Stacks 0EP1 at `W` is

`∑_{x} α(Z_x) · [κ(x) : κ(η)]`,

the sum over the points `x` of `|X|` over `η` whose integral closed subspace `Z_x` carries a
nonzero coefficient. -/
theorem finsum_mul_properCycleMult_eq_finsum_fibre (f : X ⟶ Y) (k : ℤ)
    (α : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ)
    (hα : ∀ Z, α Z ≠ 0 → deltaDimension D sX Z = k)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k) :
    ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        α Z * properCycleMult D sX hX sY hY f Z W =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x =
            W.ambientGenericPoint D.site D.base D.base_mem ∧
          α (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
            (D.isDecentSpace_of_isGood sX hX) x) ≠ 0},
        α (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
            (D.isDecentSpace_of_isGood sX hX) x) *
          (cycleResidueDegree D sX hX sY hY f x : ℤ) := by
  classical
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  set S' := {Z : IntegralClosedSubspace D.site D.base D.base_mem X | α Z ≠ 0 ∧
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z = W}
  have hsupp : (Function.support fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α Z * properCycleMult D sX hX sY hY f Z W) ⊆ S' := fun Z hZ =>
    ⟨left_ne_zero_of_mul hZ,
      ((properCycleMult_ne_zero_iff D sX hX sY hY f Z W).1 (right_ne_zero_of_mul hZ)).1⟩
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ S'
    (fun Z hZ => ⟨fun _ => hsupp hZ, fun _ => Set.mem_univ Z⟩)]
  refine finsum_mem_eq_of_bijOn _
    (bijOn_ambientGenericPoint_cycleSupport_fibre D sX hX sY hY f α W) ?_
  rintro Z ⟨hne, him⟩
  have hδ : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 hYdec f Z) = deltaDimension D sX Z := by rw [him, hW, hα Z hne]
  have hdeg : properCycleMult D sX hX sY hY f Z W =
      (cycleResidueDegree D sX hX sY hY f
        (Z.ambientGenericPoint D.site D.base D.base_mem) : ℤ) := by
    rw [properCycleMult, ite_eq_left him, properCycleDegree, ite_eq_left hδ]
    rfl
  rw [hdeg, IntegralClosedSubspace.integralClosedSubspaceOfPoint_ambientGenericPoint D.site
    D.base D.base_mem hX.1 hXdec Z]

end AlgebraicGeometry.Space

end
