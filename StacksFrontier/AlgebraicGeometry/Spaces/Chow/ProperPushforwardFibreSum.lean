module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FiniteLocallyFreePushPull
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCoherentCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType

/-!
# The pushforward coefficient of the cycle of a module, as a sum over a fibre

In Situation 0EDT let `f : X ⟶ Y` be a morphism over the base of good algebraic spaces, let `F`
be a coherent `𝒪_X`-module with `dim_δ(Supp(F)) ≤ k` and let `W ⊂ Y` be an integral closed
subspace of δ-dimension `k` with generic point `η`. The coefficient of `W` in the pushforward
`f_*[F]_k` of Stacks 0EP1 is a sum over the integral closed subspaces of `X`. This file rewrites
it as a sum over the finite set of points

`P = {x ∈ Supp(F) | f(x) = η}`,

each point `x` contributing the length of `F` at `x` times the residue degree `[κ(x) : κ(η)]`.

## Main results

* `AlgebraicGeometry.Space.inducedDimensionValue_eq_of_mem_moduleSupport_of_pointsMap_eq`: a
  point of `P` has δ-value `k`.
* `AlgebraicGeometry.Space.finite_moduleSupport_fibre`: `P` is finite, for a quasi-compact `f`.
* `AlgebraicGeometry.Space.finsum_cycleCoeffOfModule_mul_properCycleMult_eq_finsum_fibre`: the
  coefficient of `W` in `f_*[F]_k`, as the sum over `P`.

## References

* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EP3](https://stacks.math.columbia.edu/tag/0EP3)
* [Stacks Project, Tag 0EE6](https://stacks.math.columbia.edu/tag/0EE6)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)

include hY in
/-- A point of the support of `F` lying over the generic point of an integral closed subspace
`W ⊂ Y` of δ-dimension `k` has δ-value `k`, when `dim_δ(Supp(F)) ≤ k`. -/
theorem inducedDimensionValue_eq_of_mem_moduleSupport_of_pointsMap_eq {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k)
    {x : points D.site D.base D.base_mem X}
    (hxF : x ∈ moduleSupport D.site D.base D.base_mem hX.1 F)
    (hxW : pointsMap D.site D.base D.base_mem X f x =
      W.ambientGenericPoint D.site D.base D.base_mem) :
    inducedDimensionValue D.site D.base D.base_mem D.delta sX x = k := by
  have hle := (deltaDimensionClosed_le_coe_iff D sX hX _ _ k).mp hdimF x hxF
  have hge := inducedDimensionValue_pointsMap_le D sX hX sY hY f hfB x
  have hWk : inducedDimensionValue D.site D.base D.base_mem D.delta sY
      (W.ambientGenericPoint D.site D.base D.base_mem) = k := hW
  rw [hxW, hWk] at hge
  omega

include sX hX in
/-- A good algebraic space is étale locally Noetherian. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isGood :
    HasEtaleLocalProperty D.site D.base D.base_mem X
      (fun V : Scheme.{u} => IsLocallyNoetherian V) :=
  hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base
    D.base_mem hX.1 D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian

/-- A point of the support of `F` at which the δ-value attains the bound `k` has positive finite
length. -/
theorem geometricLength_toNat_ne_zero_of_inducedDimensionValue_eq
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    {x : points D.site D.base D.base_mem X}
    (hxF : x ∈ moduleSupport D.site D.base D.base_mem hX.1 F)
    (hxk : inducedDimensionValue D.site D.base D.base_mem D.delta sX x = k)
    (xbar : GeometricPoint D.site D.base D.base_mem X) (hxbar : xbar.LiesOver x) :
    (geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ xbar F).toNat ≠ 0 := by
  obtain ⟨C, hC⟩ := isGenericPoint_of_deltaDimensionClosed_le D sX hX _
    (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) x hxF k hdimF hxk
  obtain ⟨hne, hpos⟩ := geometricLength_ne_top_and_pos_of_isGenericPoint_supportOfSheaf
    D.site D.base D.base_mem ⟨X, hX.1⟩
    (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX)
    (D.isDecentSpace_of_isGood sX hX) F hxF C hC xbar hxbar
  intro h
  rcases ENat.toNat_eq_zero.mp h with h0 | htop
  · exact (ne_of_gt hpos) h0
  · exact hne htop

include hY in
/-- **The fibre of the support over the generic point of `W`, indexed by integral closed
subspaces.** Taking generic points is a bijection from the integral closed subspaces `Z ⊂ X` of
δ-dimension `k` with generic point in `Supp(F)` and image closure `W` onto the points of
`Supp(F)` over the generic point of `W`. -/
theorem bijOn_ambientGenericPoint_moduleSupport_fibre {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k) :
    Set.BijOn (fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
        Z.ambientGenericPoint D.site D.base D.base_mem)
      {Z | deltaDimension D sX Z = k ∧
        IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
          (D.isDecentSpace_of_isGood sY hY) f Z = W ∧
        Z.ambientGenericPoint D.site D.base D.base_mem ∈
          moduleSupport D.site D.base D.base_mem hX.1 F}
      {x | pointsMap D.site D.base D.base_mem X f x =
          W.ambientGenericPoint D.site D.base D.base_mem ∧
        x ∈ moduleSupport D.site D.base D.base_mem hX.1 F} := by
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hYdec := D.isDecentSpace_of_isGood sY hY
  refine ⟨fun Z hZ => ⟨?_, hZ.2.2⟩, fun Z₁ hZ₁ Z₂ hZ₂ h => ?_, fun x hx => ?_⟩
  · rw [← IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
      hX.1 hY.1 hYdec f Z, hZ.2.1]
  · refine eq_of_mem_subspacePointSet_ambientGenericPoint D sX hX Z₂ Z₁ ?_
      (hZ₁.1.trans hZ₂.1.symm)
    change Z₁.ambientGenericPoint D.site D.base D.base_mem = _ at h
    rw [h]
    exact (Z₂.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).mem
  · set Z := integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x with hZdef
    have hξ : Z.ambientGenericPoint D.site D.base D.base_mem = x :=
      pointsMap_genericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1 hXdec x
    have hxk := inducedDimensionValue_eq_of_mem_moduleSupport_of_pointsMap_eq D sX hX sY hY hfB F
      k hdimF W hW hx.2 hx.1
    have hZk : deltaDimension D sX Z = k := by
      show inducedDimensionValue D.site D.base D.base_mem D.delta sX
        (Z.ambientGenericPoint D.site D.base D.base_mem) = k
      rw [hξ, hxk]
    have himξ : (IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f
        Z).ambientGenericPoint D.site D.base D.base_mem =
          W.ambientGenericPoint D.site D.base D.base_mem := by
      rw [IntegralClosedSubspace.ambientGenericPoint_closureImage_eq D.site D.base D.base_mem
        hX.1 hY.1 hYdec f Z, hξ, hx.1]
    have him : IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z =
        W := by
      refine eq_of_mem_subspacePointSet_ambientGenericPoint D sY hY W _ ?_ ?_
      · rw [himξ]
        exact (W.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).mem
      · show inducedDimensionValue D.site D.base D.base_mem D.delta sY
          ((IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f
            Z).ambientGenericPoint D.site D.base D.base_mem) =
          inducedDimensionValue D.site D.base D.base_mem D.delta sY
            (W.ambientGenericPoint D.site D.base D.base_mem)
        rw [himξ]
    exact ⟨Z, ⟨hZk, him, hξ ▸ hx.2⟩, hξ⟩

include hY in
/-- **The coefficient of `W` in `f_*[F]_k` as a sum over the fibre of the support.** For an
integral closed subspace `W ⊂ Y` of δ-dimension `k` with generic point `η`, the defining sum of
the pushforward coefficient of Stacks 0EP1 at `W` is

`∑_{x ∈ Supp(F), f(x) = η} length_x(F) · [κ(x) : κ(η)]`. -/
theorem finsum_cycleCoeffOfModule_mul_properCycleMult_eq_finsum_fibre {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k) :
    ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        cycleCoeffOfModule D sX hX F k γX Z * properCycleMult D sX hX sY hY f Z W =
      ∑ᶠ x ∈ {x | pointsMap D.site D.base D.base_mem X f x =
          W.ambientGenericPoint D.site D.base D.base_mem ∧
        x ∈ moduleSupport D.site D.base D.base_mem hX.1 F},
        ((geometricLength D.site D.base D.base_mem ⟨X, hX.1⟩ (γX x) F).toNat : ℤ) *
          (cycleResidueDegree D sX hX sY hY f x : ℤ) := by
  classical
  have hYdec := D.isDecentSpace_of_isGood sY hY
  set S' := {Z : IntegralClosedSubspace D.site D.base D.base_mem X | deltaDimension D sX Z = k ∧
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1 hYdec f Z = W ∧
    Z.ambientGenericPoint D.site D.base D.base_mem ∈
      moduleSupport D.site D.base D.base_mem hX.1 F} with hS'
  have hsupp : (Function.support fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      cycleCoeffOfModule D sX hX F k γX Z * properCycleMult D sX hX sY hY f Z W) ⊆ S' := by
    intro Z hZ
    have hco : cycleCoeffOfModule D sX hX F k γX Z ≠ 0 := left_ne_zero_of_mul hZ
    have hm : properCycleMult D sX hX sY hY f Z W ≠ 0 := right_ne_zero_of_mul hZ
    have hZk : deltaDimension D sX Z = k := by
      by_contra h
      exact hco (by rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_right h])
    refine ⟨hZk, ((properCycleMult_ne_zero_iff D sX hX sY hY f Z W).1 hm).1, ?_⟩
    by_contra h
    refine hco ?_
    rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hZk,
      moduleMultiplicity_eq_zero_of_notMem_moduleSupport D.site D.base D.base_mem hX.1 F γX hγX
        Z h]
    rfl
  rw [← finsum_mem_univ, finsum_mem_inter_support_eq' _ _ S'
    (fun Z hZ => ⟨fun _ => hsupp hZ, fun _ => Set.mem_univ Z⟩)]
  refine finsum_mem_eq_of_bijOn _
    (bijOn_ambientGenericPoint_moduleSupport_fibre D sX hX sY hY hfB F k hdimF W hW) ?_
  rintro Z ⟨hZk, him, -⟩
  have hdeg : properCycleMult D sX hX sY hY f Z W =
      (cycleResidueDegree D sX hX sY hY f (Z.ambientGenericPoint D.site D.base D.base_mem) :
        ℤ) := by
    have hδ : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hY.1 hYdec f Z) = deltaDimension D sX Z := by rw [him, hW, hZk]
    rw [properCycleMult, ite_eq_left him, properCycleDegree, ite_eq_left hδ]
    rfl
  rw [hdeg, cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hZk]
  rfl

include hY in
/-- **The fibre of the support over the generic point of `W` is finite**, for a quasi-compact
`f`. -/
theorem finite_moduleSupport_fibre {f : X ⟶ Y} (hfB : f ≫ sY = sX)
    (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    [IsCoherent D.site D.base D.base_mem X hX.1 F] (k : ℤ)
    (hdimF : deltaDimensionClosed D sX hX (moduleSupport D.site D.base D.base_mem hX.1 F)
      (isClosed_moduleSupport D.site D.base D.base_mem hX.1 F) ≤ (k : EInt))
    (γX : points D.site D.base D.base_mem X → GeometricPoint D.site D.base D.base_mem X)
    (hγX : ∀ x, (γX x).LiesOver x)
    (W : IntegralClosedSubspace D.site D.base D.base_mem Y) (hW : deltaDimension D sY W = k) :
    {x | pointsMap D.site D.base D.base_mem X f x =
        W.ambientGenericPoint D.site D.base D.base_mem ∧
      x ∈ moduleSupport D.site D.base D.base_mem hX.1 F}.Finite := by
  have hbij := bijOn_ambientGenericPoint_moduleSupport_fibre D sX hX sY hY hfB F k hdimF W hW
  rw [← hbij.image_eq]
  refine Set.Finite.image _ ((finite_properCycleFibre D sX hX sY hY hfB hf
    (cycleCoeffOfModule D sX hX F k γX)
    (cycleCoeffOfModule_mem_cyclesOfDimension D sX hX F k γX hγX hdimF).1 W).subset ?_)
  rintro Z ⟨hZk, him, hZF⟩
  refine ⟨?_, him⟩
  rw [cycleCoeffOfModule_eq_moduleMultiplicity, ite_eq_left hZk]
  exact_mod_cast geometricLength_toNat_ne_zero_of_inducedDimensionValue_eq D sX hX F k hdimF hZF
    hZk _ (hγX _)

end AlgebraicGeometry.Space

end
