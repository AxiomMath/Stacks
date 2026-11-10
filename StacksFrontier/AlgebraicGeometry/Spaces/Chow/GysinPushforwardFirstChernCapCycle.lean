module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalGysinRule

/-!
# The pushforward of the refined Gysin map against the cap product, at the level of cycles

In Situation 0EDT let `X/B` be good, let `E ⊆ X` be a closed subspace with closed immersion
`i : E → X`, and let `k ∈ ℤ`. For a `(k+1)`-cycle `α = ∑ n_W [W]` on `X`, this file compares
`i_* i^* α`, the pushforward along `i` of the refined Gysin map, with `c₁(ℒ) ∩ α`, the cap
product with the first Chern class of an invertible sheaf `ℒ`.

The difference `i_* i^* α - c₁(ℒ) ∩ α` is the locally finite sum, over the subspaces `W ⊄ E`
occurring in `α`, of the pushforwards along `W → X` of the cycles `n_W (G_W - c₁(ℒ|_W) ∩ [W])` on
`W`, for any cycles `G_W` on `W` whose pushforward to `X` is that of `[E ∩ W]_k`. The identity
holds for an arbitrary component rule of the refined Gysin map and an arbitrary component datum of
the cap product, as long as the rule on the subspaces `W ⊆ E` is that datum.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.pushforward_pushforward` and
  `AlgebraicGeometry.Space.cycleGroupClosedPushforward_cycleGroupClosedPushforward`: pushforward
  along closed immersions is functorial, on integral closed subspaces and on cycles.
* `AlgebraicGeometry.Space.closedSubspaceCyclePushforward_containedPushforward`: for an integral
  closed subspace `W ⊆ E`, pushing forward along `W → E` and then along `E → X` is pushing
  forward along `W → X`.
* `AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinCycleMap_apply`: `i_*` commutes
  with the locally finite sum defining the refined Gysin map.
* `AlgebraicGeometry.Space.closedSubspaceCyclePushforward_gysinCycleMap_sub_firstChernCapCycleMap`:
  the identity of cycles described above.

## References

* [Stacks Project, Tag 0ER4](https://stacks.math.columbia.edu/tag/0ER4)
* [Stacks Project, Tag 0ER1](https://stacks.math.columbia.edu/tag/0ER1)
* [Stacks Project, Tag 0EQJ](https://stacks.math.columbia.edu/tag/0EQJ)
* [Stacks Project, Tag 0EQ6](https://stacks.math.columbia.edu/tag/0EQ6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### Functoriality of pushforward along closed immersions -/

section Functoriality

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The image of an integral closed subspace along a composite of closed immersions is the image
of its image. -/
theorem IntegralClosedSubspace.pushforward_pushforward (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    (hXdec : IsDecentSpace B S hS X) (hYdec : IsDecentSpace B S hS Y)
    {i : Z ⟶ Y} {j : Y ⟶ X} {l : Z ⟶ X} (hij : i ≫ j = l)
    (hi : IsClosedImmersion B S hS i) (hj : IsClosedImmersion B S hS j)
    (hl : IsClosedImmersion B S hS l) (W : IntegralClosedSubspace B S hS Z) :
    IntegralClosedSubspace.pushforward B S hS hX hY hXdec hj
        (IntegralClosedSubspace.pushforward B S hS hY hZ hYdec hi W) =
      IntegralClosedSubspace.pushforward B S hS hX hZ hXdec hl W := by
  subst hij
  refine injective_integralClosedSubspaceSupport B S hS hX (IrreducibleCloseds.ext ?_)
  change subspacePointSet B S hS X _ = subspacePointSet B S hS X _
  rw [IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_pushforward,
    IntegralClosedSubspace.subspacePointSet_pushforward, Set.image_image, pointsMap_comp]
  rfl

end Functoriality

section CycleFunctoriality

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y Z : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hY : IsAlgebraicSpace D.site D.base D.base_mem Y)
    (hZ : IsAlgebraicSpace D.site D.base D.base_mem Z)
    (hXdec : IsDecentSpace D.site D.base D.base_mem X)
    (hYdec : IsDecentSpace D.site D.base D.base_mem Y)
    {i : Z ⟶ Y} {j : Y ⟶ X} {l : Z ⟶ X} (hij : i ≫ j = l)
    (hi : IsClosedImmersion D.site D.base D.base_mem i)
    (hj : IsClosedImmersion D.site D.base D.base_mem j)
    (hl : IsClosedImmersion D.site D.base D.base_mem l)

include hij in
/-- Pushforward of coefficient families along closed immersions is functorial. -/
theorem cycleClosedPushforward_cycleClosedPushforward
    (β : IntegralClosedSubspace D.site D.base D.base_mem Z → ℤ) :
    cycleClosedPushforward D hX hY hXdec hj (cycleClosedPushforward D hY hZ hYdec hi β) =
      cycleClosedPushforward D hX hZ hXdec hl β := by
  funext V
  by_cases hV : ∃ W, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hZ hXdec hl
      W = V
  · obtain ⟨W, rfl⟩ := hV
    conv_rhs => rw [cycleClosedPushforward_apply_pushforward]
    rw [← IntegralClosedSubspace.pushforward_pushforward hX hY hZ hXdec hYdec hij hi hj hl W,
      cycleClosedPushforward_apply_pushforward, cycleClosedPushforward_apply_pushforward]
  · rw [cycleClosedPushforward_apply_of_forall_ne D hX hZ hXdec hl β V fun W hW => hV ⟨W, hW⟩]
    by_cases hV' : ∃ U, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX hY hXdec hj
        U = V
    · obtain ⟨U, rfl⟩ := hV'
      rw [cycleClosedPushforward_apply_pushforward]
      refine cycleClosedPushforward_apply_of_forall_ne D hY hZ hYdec hi β U fun W hW => hV ⟨W, ?_⟩
      rw [← IntegralClosedSubspace.pushforward_pushforward hX hY hZ hXdec hYdec hij hi hj hl W, hW]
    · exact cycleClosedPushforward_apply_of_forall_ne D hX hY hXdec hj _ V
        fun U hU => hV' ⟨U, hU⟩

include hij in
/-- Pushforward of `k`-cycles along closed immersions over the base is functorial. -/
theorem cycleGroupClosedPushforward_cycleGroupClosedPushforward (sX : X ⟶ D.space)
    (hsX : IsLocallyOfFiniteType D.site D.base D.base_mem sX) (sY : Y ⟶ D.space)
    (hsY : IsLocallyOfFiniteType D.site D.base D.base_mem sY) (sZ : Z ⟶ D.space)
    (hjc : j ≫ sX = sY) (hic : i ≫ sY = sZ) (hlc : l ≫ sX = sZ) (k : ℤ)
    (β : CycleGroup D sZ k) :
    cycleGroupClosedPushforward D hX hY hXdec hj sX hsX sY hjc k
        (cycleGroupClosedPushforward D hY hZ hYdec hi sY hsY sZ hic k β) =
      cycleGroupClosedPushforward D hX hZ hXdec hl sX hsX sZ hlc k β :=
  Subtype.ext (cycleClosedPushforward_cycleClosedPushforward D hX hY hZ hXdec hYdec hij hi hj hl
    β.1)

end CycleFunctoriality

/-! ### Pushforward along the inclusion of a closed subspace -/

section ClosedSubspace

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (k : ℤ)

/-- The pushforward `i_* : Z_k(E) → Z_k(X)` along the closed immersion `i : E → X` of a closed
subspace, `E` being viewed over the base through `X`. -/
abbrev closedSubspaceCyclePushforward : CycleGroup D (E.1.ι ≫ p) k →+ CycleGroup D p k :=
  cycleGroupClosedPushforward D hp.1 E.2.1 (D.isDecentSpace_of_isGood p hp) E.2.2 p hp.2.2
    (E.1.ι ≫ p) rfl k

variable (hE : D.IsGood (E.1.ι ≫ p))

/-- For an integral closed subspace `W ⊆ E`, pushing a cycle forward along `W → E` and then
along `E → X` is pushing it forward along `W → X`. -/
theorem closedSubspaceCyclePushforward_containedPushforward
    {W : IntegralClosedSubspace D.site D.base D.base_mem X} (hWE : W.subspace ≤ E.1)
    (c : CycleGroup D (W.subspace.ι ≫ p) k) :
    closedSubspaceCyclePushforward D p hp E k (containedPushforward D p E hE k hWE c) =
      integralClosedSubspacePushforward D p hp W k c :=
  cycleGroupClosedPushforward_cycleGroupClosedPushforward D hp.1 E.2.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood p hp) (D.isDecentSpace_of_isGood (E.1.ι ≫ p) hE)
    (Subfunctor.homOfLe_ι hWE) (isClosedImmersion_homOfLe_of_le D E hWE) E.2.2
    W.isClosedSubspace.2 p hp.2.2 (E.1.ι ≫ p) hE.2.2 (W.subspace.ι ≫ p) rfl
    (homOfLe_comp_structure D p E hWE) rfl k c

end ClosedSubspace

/-! ### `i_* i^* α` against `c₁(ℒ) ∩ α` -/

section Comparison

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p) (E : ClosedSubspaces D.site D.base D.base_mem X)
    (hE : D.IsGood (E.1.ι ≫ p)) (k : ℤ) (rule : GysinComponentRule D p E k)

/-- The coefficient of `i_* c` at an integral closed subspace `V` of `X` is the coefficient of `c`
at the integral closed subspace of `E` pushing forward to `V`, or vanishes if there is none. -/
private theorem closedSubspaceCyclePushforward_apply_eq_or
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (∃ U, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hp.1 E.2.1
      (D.isDecentSpace_of_isGood p hp) E.2.2 U = V ∧
        ∀ c : CycleGroup D (E.1.ι ≫ p) k,
          (closedSubspaceCyclePushforward D p hp E k c).1 V = c.1 U) ∨
      ∀ c : CycleGroup D (E.1.ι ≫ p) k, (closedSubspaceCyclePushforward D p hp E k c).1 V = 0 := by
  by_cases hV : ∃ U, IntegralClosedSubspace.pushforward D.site D.base D.base_mem hp.1 E.2.1
      (D.isDecentSpace_of_isGood p hp) E.2.2 U = V
  · obtain ⟨U, rfl⟩ := hV
    exact Or.inl ⟨U, rfl, fun c => cycleClosedPushforward_apply_pushforward ..⟩
  · exact Or.inr fun c => cycleClosedPushforward_apply_of_forall_ne D hp.1 E.2.1
      (D.isDecentSpace_of_isGood p hp) E.2.2 c.1 V fun U hU => hV ⟨U, hU⟩

/-- The coefficient of `i_*(i^* α)` at an integral closed subspace of `X` is the sum of `n_W`
times the coefficient of `i_*(i^*[W])` there. -/
theorem closedSubspaceCyclePushforward_gysinCycleMap_apply (α : CycleGroup D p (k + 1))
    (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    (closedSubspaceCyclePushforward D p hp E k (gysinCycleMap D p E hE k rule α)).1 V =
      ∑ᶠ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        α.1 W * (closedSubspaceCyclePushforward D p hp E k
          (gysinComponentCycle D p E hE k rule W)).1 V := by
  rcases closedSubspaceCyclePushforward_apply_eq_or D p hp E k V with ⟨U, -, h⟩ | h
  · rw [h, gysinCycleMap_apply]
    exact finsum_congr fun W => by rw [h]
  · rw [h]
    exact (finsum_eq_zero_of_forall_eq_zero fun W => by rw [h, mul_zero]).symm

/-- At a fixed integral closed subspace of `X` only finitely many subspaces contribute to the
coefficient of `i_*(i^* α)`. -/
theorem hasFiniteSupport_closedSubspaceCyclePushforward_gysinComponentCycle
    (α : CycleGroup D p (k + 1)) (V : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Function.HasFiniteSupport fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W * (closedSubspaceCyclePushforward D p hp E k
        (gysinComponentCycle D p E hE k rule W)).1 V := by
  rcases closedSubspaceCyclePushforward_apply_eq_or D p hp E k V with ⟨U, -, h⟩ | h
  · refine (hasFiniteSupport_gysinCoeff D p E hE k rule α U).subset fun W hW => ?_
    rwa [Function.mem_support, h] at hW
  · refine Set.Finite.subset Set.finite_empty fun W hW => hW ?_
    simp only [h, mul_zero]

/-- The integral closed subspaces occurring in a `(k+1)`-cycle `α` and not contained in `E`,
with their point sets, form a locally finite family. -/
theorem locallyFinite_subspacePointSet_of_ne_zero_of_not_le (α : CycleGroup D p (k + 1)) :
    LocallyFinite fun W : {W : IntegralClosedSubspace D.site D.base D.base_mem X //
        α.1 W ≠ 0 ∧ ¬ W.subspace ≤ E.1} =>
      subspacePointSet D.site D.base D.base_mem X W.1.subspace :=
  (α.2.1.comp_injective Subtype.val_injective).subset fun W => by
    simp only [Function.comp_apply, ite_eq_right W.2.1, subset_refl]

variable (chern : FirstChernComponentCycleRule D p k)
    (hrule : ∀ W hW hWE, rule.chernCycle W hW hWE = chern W hW)
    (G : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      deltaDimension D p W = k + 1 → ¬ W.subspace ≤ E.1 → CycleGroup D (W.subspace.ι ≫ p) k)
    (hG : ∀ W hW hWE, integralClosedSubspacePushforward D p hp W k (G W hW hWE) =
      closedSubspaceCyclePushforward D p hp E k (rule.intersectionCycle W hW hWE))

include hrule hG in
/-- Let `rule` be a component rule of the refined Gysin map for the closed subspace `E ⊆ X` whose
value on the integral closed subspaces `W ⊆ E` is the component datum `chern` of the cap product,
and for every integral closed subspace `W ⊄ E` of δ-dimension `k + 1` let `G_W` be a `k`-cycle on
`W` whose pushforward to `X` is that of `i^*[W] = [E ∩ W]_k`. Then for every `(k+1)`-cycle
`α = ∑ n_W [W]` on `X`

`i_* i^* α - c₁ ∩ α = ∑_{W ⊄ E, n_W ≠ 0} (W → X)_* (n_W (G_W - c₁(ℒ|_W) ∩ [W]))`

in `Z_k(X)`, the right-hand side being a locally finite sum. -/
theorem closedSubspaceCyclePushforward_gysinCycleMap_sub_firstChernCapCycleMap
    (α : CycleGroup D p (k + 1)) :
    closedSubspaceCyclePushforward D p hp E k (gysinCycleMap D p E hE k rule α) -
        firstChernCapCycleMap D p hp k chern α =
      cycleFamilySum D p hp (fun W : {W : IntegralClosedSubspace D.site D.base D.base_mem X //
          α.1 W ≠ 0 ∧ ¬ W.subspace ≤ E.1} => W.1)
        (locallyFinite_subspacePointSet_of_ne_zero_of_not_le D p E k α) k
        (fun W => α.1 W.1 • (G W.1 (α.2.2 W.1 W.2.1) W.2.2 - chern W.1 (α.2.2 W.1 W.2.1))) := by
  refine Subtype.ext (funext fun V => ?_)
  have hdim : ∀ W, α.1 W ≠ 0 → deltaDimension D p W = k + 1 := α.2.2
  obtain ⟨F, hF⟩ : ∃ F : IntegralClosedSubspace D.site D.base D.base_mem X → ℤ, ∀ W,
      F W = if h : α.1 W ≠ 0 ∧ ¬ W.subspace ≤ E.1 then
        (integralClosedSubspacePushforward D p hp W k
          (α.1 W • (G W (hdim W h.1) h.2 - chern W (hdim W h.1)))).1 V
      else 0 := ⟨_, fun _ => rfl⟩
  have hpt : ∀ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      α.1 W * (closedSubspaceCyclePushforward D p hp E k
          (gysinComponentCycle D p E hE k rule W)).1 V -
        α.1 W * (firstChernComponentCycle D p hp k chern W).1 V = F W := by
    intro W
    by_cases hα : α.1 W = 0
    · rw [hα, zero_mul, zero_mul, sub_zero, hF, dite_eq_right (fun h => h.1 hα)]
    have hW : deltaDimension D p W = k + 1 := hdim W hα
    rw [firstChernComponentCycle_of_deltaDimension_eq D p hp k chern hW]
    by_cases hWE : W.subspace ≤ E.1
    · rw [gysinComponentCycle_of_le D p E hE k rule hW hWE,
        closedSubspaceCyclePushforward_containedPushforward D p hp E k hE hWE, hrule, sub_self,
        hF, dite_eq_right (fun h => h.2 hWE)]
    · rw [gysinComponentCycle_of_not_le D p E hE k rule hW hWE, ← hG W hW hWE, hF,
        dite_eq_left ⟨hα, hWE⟩, map_zsmul, map_sub, ← mul_sub]
      rfl
  change (closedSubspaceCyclePushforward D p hp E k (gysinCycleMap D p E hE k rule α)).1 V -
      (firstChernCapCycleMap D p hp k chern α).1 V = _
  rw [closedSubspaceCyclePushforward_gysinCycleMap_apply, firstChernCapCycleMap_apply,
    ← finsum_sub_distrib
      (hasFiniteSupport_closedSubspaceCyclePushforward_gysinComponentCycle D p hp E hE k rule α V)
      (hasFiniteSupport_firstChernCapCoeff D p hp k chern α V),
    finsum_congr hpt, cycleFamilySum_apply,
    finsum_congr fun j : {W : IntegralClosedSubspace D.site D.base D.base_mem X //
      α.1 W ≠ 0 ∧ ¬ W.subspace ≤ E.1} => ((hF j.1).trans (dite_eq_left j.2)).symm,
    finsum_subtype_eq_finsum_cond fun W : IntegralClosedSubspace D.site D.base D.base_mem X =>
      α.1 W ≠ 0 ∧ ¬ W.subspace ≤ E.1]
  refine finsum_congr fun W => ?_
  rw [finsum_eq_if]
  split_ifs with h
  · rfl
  · rw [hF, dite_eq_right h]

end Comparison

end AlgebraicGeometry.Space

end
