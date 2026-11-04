module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeFibreDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange
public import StacksFrontier.AlgebraicGeometry.FieldExtensionDescent.FiniteDegree
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.BaseChange
public import StacksCore.Tactic.StacksAttribute

/-!
# The action on cycles commutes with proper push-pull

Let `(S, δ)` be a Chow situation and let

```
X' --f--> X
|         |
v         v
Y' --g--> Y
```

be a cartesian square of schemes locally of finite type over `S` with `g` proper, realized by
the literal fibre product `X' = X ×_Y Y'`. Let `α` be a family of `r`-cycles on the fibres of
`X/Y` and let `β'` be an `e`-cycle on `Y'`. This file proves the projection formula

`f_*(g^*α ∩ β') = α ∩ g_*β'`   in   `Z_{r + e}(X)`,

where `∩` is the action `Stacks.Chow.cap` of a family of cycles on fibres and `g^*α` is the
base change `Stacks.Chow.baseChangeFamily` of the family.

## Main results

* `Stacks.Chow.properPushforward_cap_baseChangeFamily` — the projection formula.

## Implementation notes

Both sides are additive in `β'`, and on a fixed point `x` of `X` only the part of `β'`
supported on the compact set `g⁻¹(p x)` can contribute. The two sides therefore agree as soon
as they agree on each one-point cycle `Stacks.Chow.cycleComponent`; this reduction is
`Stacks.Chow.properPushforward_cap_eq_of_cycleComponents`.

For a one-point cycle supported at `y ∈ Y'` there are two cases. If the point `g y` does not
carry the delta-dimension `e`, then both sides vanish, since proper pushforward kills a
component whose delta-dimension is not preserved. Otherwise the residue field extension
`κ(y)/κ(g y)` is finite, so the induced map `m : X'_y ⟶ X_{g y}` of fibres is finite locally
free of rank `[κ(y) : κ(g y)]`, being the base change of `Spec κ(y) ⟶ Spec κ(g y)`. The
coefficients of `g^*α` on that fibre are exactly the coefficients of the flat pullback of
`α_{g y}` along `m` — the two differ only by which Chow situation computes the
delta-dimension, and the relative dimensions agree because `κ(y)/κ(g y)` is algebraic — so the
push-pull identity for a finite locally free morphism, Stacks 02RH, gives

`∑_{z ∈ m⁻¹(q)} (g^*α)_y(z) · [κ(z) : κ(q)] = [κ(y) : κ(g y)] · α_{g y}(q)`,

which is `Stacks.Chow.finsum_baseChangeFamily_residueDegree`, and that is the whole content of
the formula at a one-point cycle.

The Stacks statement restricts to `e ≥ 0`, but the action is constructed for every `e ∈ ℤ` and
the statement is given for `e : ℤ`, which generalizes it rather than weakening it.

## References

* [Stacks Project, Tag 0H6B](https://stacks.math.columbia.edu/tag/0H6B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Additivity of the two operations -/

/-- The action `α ∩ -` of a family of cycles on fibres, as a homomorphism of abelian groups. -/
def capHom (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (e : ℤ) (α : FamilyOfCycles p r) :
    CycleGroup C sY e →+ CycleGroup C (p ≫ sY) ((r : ℤ) + e) where
  toFun := cap C sY p α
  map_zero' := by
    apply Subtype.ext
    ext x
    simp [cap_apply, capCoeff]
  map_add' := cap_add_right C sY p α

/-- The action of a family of cycles on fibres kills the zero cycle. -/
theorem cap_zero_right (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) :
    cap C sY p α (0 : CycleGroup C sY e) = 0 :=
  (capHom C sY p r e α).map_zero

/-- The action of a family of cycles on fibres commutes with integer multiples. -/
theorem cap_zsmul_right (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (p : X ⟶ Y) [LocallyOfFiniteType p] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) (n : ℤ) (β : CycleGroup C sY e) :
    cap C sY p α (n • β) = n • cap C sY p α β :=
  (capHom C sY p r e α).map_zsmul n β

/-! ### Cutting a cycle into its one-point pieces -/

/-- The part of a cycle supported at a single point: the cycle whose coefficient at `y` is that
of `β` and whose other coefficients vanish. -/
def cycleComponent (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {e : ℤ} (β : CycleGroup C sY e) (y : Y) : CycleGroup C sY e := by
  classical
  exact ⟨Function.locallyFinsuppWithin.single y (β.1 y), by
    intro Z hZ
    by_cases h : Z.isIrreducible.genericPoint = y
    · exact β.2 Z (by simpa [Function.locallyFinsuppWithin.single_apply, h] using hZ)
    · simp [Function.locallyFinsuppWithin.single_apply, h] at hZ⟩

open Classical in
/-- The coefficients of a one-point piece of a cycle. -/
theorem cycleComponent_apply (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {e : ℤ} (β : CycleGroup C sY e) (y z : Y) :
    (cycleComponent C sY β y).1 z = if z = y then β.1 y else 0 :=
  Function.locallyFinsuppWithin.single_apply

/-- Reading off the coefficient of a cycle at a point, as a homomorphism of abelian groups. -/
def cycleEvaluation (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (e : ℤ) (y : Y) : CycleGroup C sY e →+ ℤ where
  toFun β := β.1 y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Two additive functionals on cycles agree at `β` as soon as each depends on `β` only through
its coefficients on a set `K` meeting the support of `β` in a finite set, and the two agree on
the one-point pieces of `β` at the points of `K`. -/
theorem eq_of_eq_on_cycleComponents (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] {e : ℤ} (β : CycleGroup C sY e) (K : Set Y)
    (hK : (K ∩ Function.support β.1).Finite) (L R : CycleGroup C sY e →+ ℤ)
    (hL : ∀ γ, (∀ y ∈ K, γ.1 y = β.1 y) → L γ = L β)
    (hR : ∀ γ, (∀ y ∈ K, γ.1 y = β.1 y) → R γ = R β)
    (h : ∀ y ∈ K, L (cycleComponent C sY β y) = R (cycleComponent C sY β y)) : L β = R β := by
  classical
  let γ := ∑ y ∈ hK.toFinset, cycleComponent C sY β y
  have hγ : ∀ y ∈ K, γ.1 y = β.1 y := by
    intro y hy
    change (cycleEvaluation C sY e y) γ = β.1 y
    dsimp only [γ]
    rw [map_sum]
    change (∑ z ∈ hK.toFinset, (cycleComponent C sY β z).1 y) = β.1 y
    simp only [cycleComponent_apply]
    by_cases hβ : β.1 y = 0
    · simp [hβ]
    · simp [Set.Finite.mem_toFinset, hy, Function.mem_support, hβ]
  rw [← hL γ hγ, ← hR γ hγ]
  simp only [γ, map_sum]
  exact Finset.sum_congr rfl fun y hy ↦ h y ((Set.Finite.mem_toFinset hK).mp hy).1

/-! ### The structure morphism of the base change -/

/-- In a square over `S` the projection `X ×_Y Y' ⟶ X` is a morphism over `S`. This is forced by
the data and is not an assumption. -/
theorem pullbackFst_comp_eq {D : Type*} [Category D] {S X Y Y' : D} {sX : X ⟶ S} {sY : Y ⟶ S}
    {f : X ⟶ Y} (g : Y' ⟶ Y) [HasPullback f g] (hf : f ≫ sY = sX) :
    pullback.fst f g ≫ sX = pullback.snd f g ≫ g ≫ sY := by
  rw [← hf, ← Category.assoc, pullback.condition, Category.assoc]

/-- In a cartesian square over `S` the two routes `X ×_Y Y' → X → S` and `X ×_Y Y' → Y' → S`
agree. This is forced by the data and is not an assumption. -/
theorem pullbackFst_comp_eq_of_base {D : Type*} [Category D] {S X Y Y' : D} {sX : X ⟶ S}
    {sY : Y ⟶ S} {sY' : Y' ⟶ S} {f : X ⟶ Y} (g : Y' ⟶ Y) [HasPullback f g]
    (hf : f ≫ sY = sX) (hg : g ≫ sY = sY') :
    pullback.fst f g ≫ sX = pullback.snd f g ≫ sY' := by
  rw [← hg]
  exact pullbackFst_comp_eq g hf

/-- The two projections of a pullback have the same image in the base. -/
private theorem apply_fst_eq_apply_snd {X Y Y' : Scheme.{u}} (p : X ⟶ Y) (g : Y' ⟶ Y)
    (z : ↥(pullback p g : Scheme.{u})) : p (pullback.fst p g z) = g (pullback.snd p g z) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun q : pullback p g ⟶ Y => q z) (pullback.condition (f := p) (g := g))

/-! ### Reduction to one-point cycles -/

/-- The projection formula follows from its special case at the one-point pieces of `β`: both
sides are additive in `β`, and the coefficient of either at a point `x` of `X` depends only on
the coefficients of `β` on the compact set `g⁻¹(p x)`. -/
theorem properPushforward_cap_eq_of_cycleComponents (C : ChowSituation.{u})
    {X Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y)
    [LocallyOfFiniteType p] (g : Y' ⟶ Y) [IsProper g] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) (β : CycleGroup C (g ≫ sY) e)
    (h : ∀ y : Y',
      properPushforward C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY) (pullback.fst p g)
          (pullbackFst_comp_eq g rfl) ((r : ℤ) + e)
          (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α)
            (cycleComponent C (g ≫ sY) β y)) =
        cap C sY p α
          (properPushforward C (g ≫ sY) sY g rfl e (cycleComponent C (g ≫ sY) β y))) :
    properPushforward C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY) (pullback.fst p g)
        (pullbackFst_comp_eq g rfl) ((r : ℤ) + e)
        (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α) β) =
      cap C sY p α (properPushforward C (g ≫ sY) sY g rfl e β) := by
  classical
  apply Subtype.ext
  ext x
  let α' := baseChangeFamily p g r α
  let L := (cycleEvaluation C (p ≫ sY) ((r : ℤ) + e) x).comp
    ((properPushforwardHom C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY) (pullback.fst p g)
      (pullbackFst_comp_eq g rfl) ((r : ℤ) + e)).comp
      (capHom C (g ≫ sY) (pullback.snd p g) r e α'))
  let R := ((cycleEvaluation C (p ≫ sY) ((r : ℤ) + e) x).comp
    (capHom C sY p r e α)).comp (properPushforwardHom C (g ≫ sY) sY g rfl e)
  change L β = R β
  apply eq_of_eq_on_cycleComponents C (g ≫ sY) β (g ⁻¹' {p x})
    (β.1.locallyFiniteSupport.finite_inter_support_of_isCompact
      (g.isCompact_preimage_singleton (p x))) L R
  · intro γ hγ
    change (properPushforward C _ _ _ (pullbackFst_comp_eq g rfl) _ (cap C _ _ α' γ)).1 x =
      (properPushforward C _ _ _ (pullbackFst_comp_eq g rfl) _ (cap C _ _ α' β)).1 x
    simp only [properPushforward_apply, cap_apply, capCoeff]
    apply finsum_mem_congr rfl
    intro z hz
    have hz' : (pullback.fst p g) z = x := hz
    rw [hγ ((pullback.snd p g) z) 
      (by change g _ = p x; rw [← apply_fst_eq_apply_snd p g z, hz'])]
  · intro γ hγ
    change capCoeff p α (properPushforward C (g ≫ sY) sY g rfl e γ).1 x =
      capCoeff p α (properPushforward C (g ≫ sY) sY g rfl e β).1 x
    unfold capCoeff
    congr 1
    simp only [properPushforward_apply]
    exact finsum_mem_congr rfl fun y hy ↦ by rw [hγ y hy]
  · intro y _
    exact congrArg (fun z : CycleGroup C (p ≫ sY) ((r : ℤ) + e) => z.1 x) (h y)

/-! ### Coefficients, dimensions and degrees -/

/-- The coefficient of a family of cycles on fibres at a point of a fibre is its coefficient at
the canonical fibre point of the image of that point in the total space. -/
theorem familyOfCycles_apply_of_fiberι {X Y : Scheme.{u}} (p : X ⟶ Y) [LocallyOfFiniteType p]
    {r : ℕ} (α : FamilyOfCycles p r) (y : Y) (z : p.fiber y) (x : X) (hz : p.fiberι y z = x) :
    (α y).1 z = (α (p x)).1 (p.asFiber x) := by
  have hy : p x = y := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff, Scheme.Hom.fiberHomeo_apply,
      hz] using (p.fiberHomeo y z).2
  subst y
  congr 1
  exact (p.fiberι (p x)).isEmbedding.injective (hz.trans (p.fiberι_asFiber x).symm)

/-- A base-changed family vanishes at a point of the base change whose image carries a zero
coefficient of the original family. -/
theorem baseChangeFamily_apply_eq_zero {X Y Y' : Scheme.{u}} (p : X ⟶ Y)
    [LocallyOfFiniteType p] (g : Y' ⟶ Y) (r : ℕ) (α : FamilyOfCycles p r)
    (z : (pullback p g : Scheme.{u}))
    (hα : (α (p ((pullback.fst p g) z))).1 (p.asFiber ((pullback.fst p g) z)) = 0) :
    ((baseChangeFamily p g r α) ((pullback.snd p g) z)).1 ((pullback.snd p g).asFiber z) = 0 := by
  rw [baseChangeFamily_apply]
  let m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition
    ((pullback.snd p g) z)
  have hm : p.fiberι (g ((pullback.snd p g) z)) (m ((pullback.snd p g).asFiber z)) =
      (pullback.fst p g) z := by
    have hm' : m ≫ p.fiberι _ = (pullback.snd p g).fiberι _ ≫ pullback.fst p g :=
      restrictedFiberMap_fiberι p (pullback.snd p g) (pullback.fst p g) g pullback.condition _
    change (m ≫ p.fiberι _) ((pullback.snd p g).asFiber z) = _
    rw [hm', Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]
  rw [familyOfCycles_apply_of_fiberι p α _ _ _ hm, hα, zero_mul]

/-- The one-point cycle of coefficient `1` at a point, in the cycle group of the delta-dimension
of that point. -/
def singleCycle (C : ChowSituation.{u}) {Y : Scheme.{u}} (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (y : Y) :
    CycleGroup C sY (relativeDimension C.dimensionFunction sY y) := by
  classical
  refine ⟨Function.locallyFinsuppWithin.single y (1 : ℤ), ?_⟩
  intro Z hZ
  have h : Z.isIrreducible.genericPoint = y := by
    by_contra h
    simp [Function.locallyFinsuppWithin.single_apply, h] at hZ
  simp only [deltaDimension, h]

/-- A point at which a family of `r`-cycles on the fibres of `X/Y` has a nonzero coefficient has
relative dimension over the base equal to `r` plus the relative dimension of its image. -/
theorem relativeDimension_eq_add_of_familyOfCycles_apply_ne_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y)
    [LocallyOfFiniteType p] {r : ℕ} (α : FamilyOfCycles p r) (x : X)
    (hx : (α (p x)).1 (p.asFiber x) ≠ 0) :
    relativeDimension C.dimensionFunction (p ≫ sY) x =
      (r : ℤ) + relativeDimension C.dimensionFunction sY (p x) := by
  classical
  let Z : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  have hZ : Z.isIrreducible.genericPoint = x :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq (isGenericPoint_closure (x := x))
  have hne : capCoeff p α (singleCycle C sY (p x)).1 Z.isIrreducible.genericPoint ≠ 0 := by
    rw [hZ]
    simpa [capCoeff, singleCycle] using hx
  simpa only [deltaDimension, hZ] using
    capCoeff_deltaDimension C sY p α (singleCycle C sY (p x)) Z hne

/-- A point at which a cycle of delta-dimension `e` has a nonzero coefficient has relative
dimension `e`. -/
theorem relativeDimension_eq_of_cycleGroup_apply_ne_zero (C : ChowSituation.{u})
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {e : ℤ} (β : CycleGroup C sY e)
    (y : Y) (hy : β.1 y ≠ 0) : relativeDimension C.dimensionFunction sY y = e := by
  let Z : IrreducibleCloseds Y :=
    ⟨closure ({y} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
  have hZ : Z.isIrreducible.genericPoint = y :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq (isGenericPoint_closure (x := y))
  simpa only [deltaDimension, hZ] using β.2 Z (hZ.symm ▸ hy)

/-! ### Vanishing away from the right delta-dimension -/

/-- The pushforward of a one-point piece of a cycle vanishes when the image point does not carry
the delta-dimension of the cycle. -/
theorem properPushforward_cycleComponent_eq_zero (C : ChowSituation.{u}) {Y Y' : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : Y' ⟶ Y) [IsProper g] (e : ℤ)
    (β : CycleGroup C (g ≫ sY) e) (y : Y')
    (hy : relativeDimension C.dimensionFunction sY (g y) ≠ e) :
    properPushforward C (g ≫ sY) sY g rfl e (cycleComponent C (g ≫ sY) β y) = 0 := by
  classical
  apply Subtype.ext
  ext x
  rw [properPushforward_apply]
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro z _
  by_cases hz : z = y
  · subst z
    rw [cycleComponent_apply, ite_eq_left rfl]
    by_cases hβ : β.1 y = 0
    · simp [hβ]
    · rw [ite_eq_right (by
        rw [relativeDimension_eq_of_cycleGroup_apply_ne_zero C (g ≫ sY) β y hβ]
        exact Ne.symm hy), mul_zero]
  · simp [cycleComponent_apply, hz]

/-- At a point where the base change of a family capped with a one-point piece of `β` at `y` has a
nonzero coefficient, the point lies over `y` and has the expected relative dimensions. -/
private theorem snd_eq_and_relativeDimension_of_cap_cycleComponent_ne_zero
    (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] (g : Y' ⟶ Y) [IsProper g] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) (β : CycleGroup C (g ≫ sY) e) (y : Y')
    (z : ↥(pullback p g : Scheme.{u}))
    (hz : (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α)
      (cycleComponent C (g ≫ sY) β y)).1 z ≠ 0) :
    (pullback.snd p g) z = y ∧
      relativeDimension C.dimensionFunction (pullback.snd p g ≫ g ≫ sY) z = (r : ℤ) + e ∧
      relativeDimension C.dimensionFunction (p ≫ sY) ((pullback.fst p g) z) =
        (r : ℤ) + relativeDimension C.dimensionFunction sY (g y) := by
  have hcoeff : (cycleComponent C (g ≫ sY) β y).1 ((pullback.snd p g) z) *
      (baseChangeFamily p g r α ((pullback.snd p g) z)).1 ((pullback.snd p g).asFiber z) ≠ 0 := hz
  have hsnd : (pullback.snd p g) z = y := by
    by_contra hsnd
    simp [cycleComponent_apply, hsnd] at hcoeff
  have hα : (α (p ((pullback.fst p g) z))).1 (p.asFiber ((pullback.fst p g) z)) ≠ 0 := fun ha ↦
    (mul_ne_zero_iff.mp hcoeff).2 (baseChangeFamily_apply_eq_zero p g r α z ha)
  refine ⟨hsnd, relativeDimension_eq_of_cycleGroup_apply_ne_zero C _ _ z hz, ?_⟩
  rw [relativeDimension_eq_add_of_familyOfCycles_apply_ne_zero C sY p α _ hα,
    apply_fst_eq_apply_snd, hsnd]

/-- The left-hand side of the projection formula vanishes on a one-point piece whose image point
does not carry the delta-dimension of the cycle. -/
theorem properPushforward_cap_cycleComponent_eq_zero (C : ChowSituation.{u})
    {X Y Y' : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y)
    [LocallyOfFiniteType p] (g : Y' ⟶ Y) [IsProper g] (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) (β : CycleGroup C (g ≫ sY) e) (y : Y')
    (hy : relativeDimension C.dimensionFunction sY (g y) ≠ e) :
    properPushforward C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY) (pullback.fst p g)
        (pullbackFst_comp_eq g rfl) ((r : ℤ) + e)
        (cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α)
          (cycleComponent C (g ≫ sY) β y)) = 0 := by
  classical
  let γ := cap C (g ≫ sY) (pullback.snd p g) (baseChangeFamily p g r α)
    (cycleComponent C (g ≫ sY) β y)
  apply Subtype.ext
  ext x
  rw [properPushforward_apply]
  apply finsum_mem_eq_zero_of_forall_eq_zero
  intro z _
  change γ.1 z * _ = 0
  by_cases hγ : γ.1 z = 0
  · rw [hγ, zero_mul]
  · obtain ⟨-, hdimZ, hdimX⟩ :=
      snd_eq_and_relativeDimension_of_cap_cycleComponent_ne_zero C sY p g r e α β y z hγ
    rw [hdimZ, hdimX, ite_eq_right (by omega), mul_zero]

/-! ### The fibre map of a base change -/

section FiberMap

variable {X Y Y' : Scheme.{u}} (p : X ⟶ Y) (g : Y' ⟶ Y)

/-- The map of fibres `(X ×_Y Y')_y ⟶ X_{g y}` is the base change of
`Spec κ(y) ⟶ Spec κ(g y)` along the structure morphism of the fibre `X_{g y}`. -/
theorem restrictedFiberMap_isPullback (y : Y') :
    IsPullback (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g
        pullback.condition y)
      ((pullback.snd p g).fiberToSpecResidueField y) (p.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback p g) y

/-- The residue degree of a point in a fibre of the base change, measured along the map of
fibres, is its residue degree along the projection `X ×_Y Y' ⟶ X`. -/
theorem restrictedFiberMap_residueDegree (y : Y') (z : (pullback.snd p g).fiber y) :
    (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition
        y).residueDegree z =
      (pullback.fst p g).residueDegree ((pullback.snd p g).fiberι y z) := by
  have hm := restrictedFiberMap_fiberι p (pullback.snd p g) (pullback.fst p g) g
    pullback.condition y
  have h := congrArg (fun q ↦ Scheme.Hom.residueDegree q z) hm
  simpa only [residueDegree_comp, residueDegree_eq_one_of_isPreimmersion, mul_one,
    one_mul] using h

/-- The map of fibres is finite when the residue field extension is. -/
theorem restrictedFiberMap_isFinite (y : Y')
    (h : letI := (g.residueFieldMap y).hom.toAlgebra
      FiniteDimensional (Y.residueField (g y)) (Y'.residueField y)) :
    IsFinite (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g
      pullback.condition y) := by
  have hfinite : IsFinite (Spec.map (g.residueFieldMap y)) := (IsFinite.SpecMap_iff _).mpr h
  exact MorphismProperty.of_isPullback (restrictedFiberMap_isPullback p g y).flip hfinite

/-- The map of fibres is flat, being the base change of a morphism of spectra of fields. -/
theorem restrictedFiberMap_flat (y : Y') :
    Flat (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y) := by
  have hflat : Flat (Spec.map (g.residueFieldMap y)) := by
    rw [Flat.SpecMap_iff]
    let := (g.residueFieldMap y).hom.toAlgebra
    change Module.Flat (Y.residueField (g y)) (Y'.residueField y)
    infer_instance
  exact MorphismProperty.of_isPullback (restrictedFiberMap_isPullback p g y).flip hflat

/-- The map of fibres is finite locally free of rank the residue degree of `y`. -/
theorem restrictedFiberMap_isFiniteLocallyFreeOfRank (y : Y')
    (h : letI := (g.residueFieldMap y).hom.toAlgebra
      FiniteDimensional (Y.residueField (g y)) (Y'.residueField y)) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y)
      (g.residueDegree y) := by
  let : Algebra (Y.residueField (g y)) (Y'.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  let : FiniteDimensional (Y.residueField (g y)) (Y'.residueField y) := h
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Spec.map (g.residueFieldMap y))
      (g.residueDegree y) :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_SpecMap_algebraMap
      (Y.residueField (g y)) (Y'.residueField y)
  exact Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback
    (restrictedFiberMap_isPullback p g y).flip

/-- A sum over the fibre of the map of fibres above a point `q` is the sum over the points of
`X ×_Y Y'` lying over the image of `q` in `X` and over `y` in `Y'`. -/
theorem finsum_restrictedFiberMap_eq (y : Y') (q : p.fiber (g y)) {M : Type*} [AddCommMonoid M]
    (w : ↥(pullback p g : Scheme.{u}) → M) :
    (∑ᶠ z ∈ (restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g
        pullback.condition y) ⁻¹' {q}, w ((pullback.snd p g).fiberι y z)) =
      ∑ᶠ z ∈ (pullback.fst p g) ⁻¹' {p.fiberι (g y) q} ∩ (pullback.snd p g) ⁻¹' {y}, w z := by
  let m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
  have hm : m ≫ p.fiberι (g y) = (pullback.snd p g).fiberι y ≫ pullback.fst p g :=
    restrictedFiberMap_fiberι p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
  apply finsum_mem_eq_of_bijOn ((pullback.snd p g).fiberι y)
  · refine ⟨?_, (pullback.snd p g).fiberι y |>.isEmbedding.injective.injOn, ?_⟩
    · intro z hz
      refine ⟨?_, ((pullback.snd p g).fiberHomeo y z).2⟩
      change (pullback.fst p g) ((pullback.snd p g).fiberι y z) = p.fiberι (g y) q
      change m z = q at hz
      simpa only [Scheme.Hom.comp_apply, hz] using (congrArg (fun k ↦ k z) hm).symm
    · intro z hz
      let v := ((pullback.snd p g).fiberHomeo y).symm ⟨z, hz.2⟩
      have hv : (pullback.snd p g).fiberι y v = z :=
        (pullback.snd p g).fiberι_fiberHomeo_symm y ⟨z, hz.2⟩
      refine ⟨v, ?_, hv⟩
      change m v = q
      apply (p.fiberι (g y)).isEmbedding.injective
      have hw := congrArg (fun k ↦ k v) hm
      simp only [Scheme.Hom.comp_apply, hv] at hw
      exact hw.trans hz.1
  · intro z _
    rfl

end FiberMap

/-! ### Identifying the base-changed family with a flat pullback -/

/-- The multiplicity of a point in a closed subscheme does not depend on the Chow situation
computing delta-dimensions, as long as the two dimension conditions agree. -/
theorem closedSubschemeCycleCoeff_eq_of_relativeDimension_iff (C D : ChowSituation.{u})
    {X Z : Scheme.{u}} (s : X ⟶ C.S) [LocallyOfFiniteType s] (t : X ⟶ D.S)
    [LocallyOfFiniteType t] (i : Z ⟶ X) [IsClosedImmersion i] (k l : ℤ) (x : X)
    (h : relativeDimension C.dimensionFunction s x = k ↔
      relativeDimension D.dimensionFunction t x = l) :
    closedSubschemeCycleCoeff C s i k x = closedSubschemeCycleCoeff D t i l x := by
  classical
  unfold closedSubschemeCycleCoeff
  have hiff : (∃ ξ : genericPoints Z,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction s x = k) ↔
      ∃ ξ : genericPoints Z, i ξ.1 = x ∧ relativeDimension D.dimensionFunction t x = l := by
    simp only [h]
  by_cases hc : ∃ ξ : genericPoints Z,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction s x = k
  · have hd := hiff.mp hc
    rw [dite_eq_left hc, dite_eq_left hd]
    congr 1
    exact Subtype.ext (i.isClosedEmbedding.injective
      ((Classical.choose_spec hc).1.trans (Classical.choose_spec hd).1.symm))
  · rw [dite_eq_right hc, dite_eq_right (hc ∘ hiff.mpr)]

/-- A finite morphism to a scheme has finite residue field extensions at closed points. -/
@[ega "I 6.4.2" "special case"]
theorem finiteDimensional_residueField_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (Y.residueField (f x)) (X.residueField x) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.range_fromSpecResidueField]; exact hx)
  have : IsFinite (Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField (f x)) := by
    rw [f.SpecMap_residueFieldMap_fromSpecResidueField]
    infer_instance
  have : IsFinite (Spec.map (f.residueFieldMap x)) :=
    IsFinite.of_comp _ (Y.fromSpecResidueField (f x))
  exact (IsFinite.SpecMap_iff _).mp inferInstance

/-- Relative dimension over the spectrum of a field is unchanged by a finite extension of that
field. -/
theorem relativeDimension_fieldChowSituation_comp {K L : Type u} [Field K] [Field L]
    (f : Spec (.of L) ⟶ Spec (.of K)) [IsFinite f] {Z : Scheme.{u}}
    (t : Z ⟶ Spec (.of L)) (z : Z) :
    relativeDimension (fieldChowSituation K).dimensionFunction (t ≫ f) z =
      relativeDimension (fieldChowSituation L).dimensionFunction t z := by
  let k := (Spec (.of K)).residueField (f (t z))
  let l := (Spec (.of L)).residueField (t z)
  let A := Z.residueField z
  let : Algebra k l := (f.residueFieldMap (t z)).hom.toAlgebra
  let : Algebra l A := (t.residueFieldMap z).hom.toAlgebra
  let : Algebra k A := ((t ≫ f).residueFieldMap z).hom.toAlgebra
  let : FiniteDimensional k l :=
    finiteDimensional_residueField_of_isFinite f (t z) isClosed_singleton
  let : IsScalarTower k l A := IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun ψ ↦ ψ.hom a) (Scheme.residueFieldMap_comp t f z)
  have htr := trdeg_add_eq k l (A := A)
  rw [trdeg_eq_zero (R := k) (A := l), zero_add] at htr
  unfold relativeDimension
  rw [fieldChowSituation_dimensionFunction_eq_zero, fieldChowSituation_dimensionFunction_eq_zero]
  exact congrArg (fun c : Cardinal ↦ (0 : ℤ) + (Cardinal.toNat c : ℤ)) htr.symm

/-- The coefficients of the base change of a family of cycles along a morphism with finite
residue field extension at `y` are the coefficients of the flat pullback of the member over
`g y` along the map of fibres. -/
theorem baseChangeFamily_eq_flatPullbackCoeff {X Y Y' : Scheme.{u}} (p : X ⟶ Y)
    [LocallyOfFiniteType p] (g : Y' ⟶ Y) (r : ℕ) (α : FamilyOfCycles p r) (y : Y')
    (hfinite : letI := (g.residueFieldMap y).hom.toAlgebra
      FiniteDimensional (Y.residueField (g y)) (Y'.residueField y))
    (z : (pullback.snd p g).fiber y) :
    letI m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
    letI : LocallyOfFiniteType (p.fiberToSpecResidueField (g y)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField (g y))))
    letI : IsFinite m := restrictedFiberMap_isFinite p g y hfinite
    letI : LocallyOfFiniteType (m ≫ p.fiberToSpecResidueField (g y)) := inferInstance
    ((baseChangeFamily p g r α y).1) z =
      flatPullbackCoeff (fieldChowSituation (Y.residueField (g y)))
        (m ≫ p.fiberToSpecResidueField (g y)) (p.fiberToSpecResidueField (g y)) m 0 (r : ℤ)
        (α (g y)) z := by
  let m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
  have : IsFinite m := restrictedFiberMap_isFinite p g y hfinite
  have : LocallyOfFiniteType (p.fiberToSpecResidueField (g y)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField (g y))))
  have : LocallyOfFiniteType ((pullback.snd p g).fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType
      (pullback.snd (pullback.snd p g) (Y'.fromSpecResidueField y)))
  dsimp only
  rw [baseChangeFamily_apply]
  unfold flatPullbackCoeff flatPullbackWeight
  dsimp only
  congr 1
  apply closedSubschemeCycleCoeff_eq_of_relativeDimension_iff
  simp only [Nat.cast_zero, add_zero]
  have : IsFinite (Spec.map (g.residueFieldMap y)) := (IsFinite.SpecMap_iff _).mpr hfinite
  rw [(restrictedFiberMap_isPullback p g y).w]
  exact (congrArg (fun n : ℤ ↦ n = (r : ℤ))
    (relativeDimension_fieldChowSituation_comp (K := Y.residueField (g y))
      (L := Y'.residueField y) (Spec.map (g.residueFieldMap y))
      ((pullback.snd p g).fiberToSpecResidueField y) z).symm).to_iff

/-- **The degree formula on a fibre.** Summing the coefficients of the base-changed family over
the fibre of the map of fibres above a point `q`, weighted by residue degrees, gives the
residue degree of `y` times the coefficient of the original family at `q`. -/
theorem finsum_baseChangeFamily_residueDegree {X Y Y' : Scheme.{u}} (p : X ⟶ Y)
    [LocallyOfFiniteType p] (g : Y' ⟶ Y) (r : ℕ) (α : FamilyOfCycles p r) (y : Y')
    (hfinite : letI := (g.residueFieldMap y).hom.toAlgebra
      FiniteDimensional (Y.residueField (g y)) (Y'.residueField y))
    (q : p.fiber (g y)) :
    letI m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
    (∑ᶠ z ∈ m ⁻¹' {q}, ((baseChangeFamily p g r α y).1) z * (m.residueDegree z : ℤ)) =
      (g.residueDegree y : ℤ) * (α (g y)).1 q := by
  let m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g pullback.condition y
  let C := fieldChowSituation (Y.residueField (g y))
  let s := p.fiberToSpecResidueField (g y)
  let α' := baseChangeFamily p g r α y
  have : LocallyOfFiniteType s :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField (g y))))
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank m (g.residueDegree y) :=
    restrictedFiberMap_isFiniteLocallyFreeOfRank p g y hfinite
  have : LocallyOfFiniteType m :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank m (g.residueDegree y)
  have : Flat m := Stacks.Morphisms.flat_of_isFiniteLocallyFreeOfRank m (g.residueDegree y)
  have : IsProper m := Stacks.Morphisms.isProper_of_isFiniteLocallyFreeOfRank m
    (g.residueDegree y)
  have : LocallyOfFiniteType (m ≫ s) := inferInstance
  let hm : AlgebraicGeometry.RelativeDimension m 0 :=
    Stacks.Morphisms.relativeDimension_zero_of_isFiniteLocallyFreeOfRank m (g.residueDegree y)
  have hpush := congrArg (fun c : CycleGroup C s (r : ℤ) ↦ c.1 q)
    (properPushforward_flatPullback_of_isFiniteLocallyFreeOfRank C (m ≫ s) s m
      (g.residueDegree y) rfl (r : ℤ) (by simp) (α (g y)))
  simp only [properPushforward_apply] at hpush
  change (∑ᶠ z ∈ m ⁻¹' {q}, α'.1 z * (m.residueDegree z : ℤ)) = _
  rw [show ((g.residueDegree y : ℤ) * (α (g y)).1 q) =
    (((g.residueDegree y : ℤ) • α (g y) : CycleGroup C s (r : ℤ)).1 q) from rfl, ← hpush]
  refine finsum_mem_congr rfl fun z _ => ?_
  have hval : α'.1 z = (flatPullback C (m ≫ s) s m rfl 0 hm (r : ℤ) (α (g y))).1 z := by
    rw [flatPullback_apply]
    exact baseChangeFamily_eq_flatPullbackCoeff p g r α y hfinite z
  rw [hval]
  by_cases ha : (flatPullback C (m ≫ s) s m rfl 0 hm (r : ℤ) (α (g y))).1 z = 0
  · rw [ha, zero_mul, zero_mul]
  · have ha₀ : (α (g y)).1 (m z) ≠ 0 := fun h0 =>
      ha (by rw [flatPullback_apply, h0, zero_mul])
    have h₁ := relativeDimension_eq_of_cycleGroup_apply_ne_zero C (m ≫ s)
      (flatPullback C (m ≫ s) s m rfl 0 hm (r : ℤ) (α (g y))) z ha
    have h₂ := relativeDimension_eq_of_cycleGroup_apply_ne_zero C s (α (g y)) (m z) ha₀
    rw [ite_eq_left (by rw [h₁, h₂]; simp)]

/-! ### The projection formula -/

/-- A morphism over the base which does not change relative dimension at a point has a finite
residue field extension there: the transcendence degree of the extension is zero and the
extension is essentially of finite type. -/
theorem finiteDimensional_residueField_of_relativeDimension_eq {X Y S : Scheme.{u}}
    (δ : DimensionFunction S) (sY : Y ⟶ S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X)
    (h : relativeDimension δ (f ≫ sY) x = relativeDimension δ sY (f x)) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (Y.residueField (f x)) (X.residueField x) := by
  let K := S.residueField (sY (f x))
  let E := Y.residueField (f x)
  let L := X.residueField x
  let : Algebra K E := (sY.residueFieldMap (f x)).hom.toAlgebra
  let : Algebra E L := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra K L := ((f ≫ sY).residueFieldMap x).hom.toAlgebra
  let : Algebra.EssFiniteType K E :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap sY (f x))
  let : Algebra.EssFiniteType E L :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)
  have hcomp : ((f ≫ sY).residueFieldMap x).hom =
      (f.residueFieldMap x).hom.comp (sY.residueFieldMap (f x)).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp f sY x)
  let : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun a ↦
    congrArg (fun φ : K →+* L ↦ φ a) hcomp
  have htr := trdeg_add_eq K E (A := L)
  have hnat := congrArg Cardinal.toNat htr
  rw [Cardinal.toNat_add (trdeg_lt_aleph0 K E) (trdeg_lt_aleph0 E L)] at hnat
  change δ (sY (f x)) + (Cardinal.toNat (Algebra.trdeg K L) : ℤ) =
    δ (sY (f x)) + (Cardinal.toNat (Algebra.trdeg K E) : ℤ) at h
  have hzero : Cardinal.toNat (Algebra.trdeg E L) = 0 := by omega
  have htrzero : Algebra.trdeg E L = 0 :=
    (Cardinal.toNat_eq_zero.mp hzero).resolve_right (not_le_of_gt (trdeg_lt_aleph0 E L))
  let : Algebra.IsAlgebraic E L := trdeg_eq_zero_iff.mp htrzero
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- **Stacks Project, Tag 0H6B.** Let `(S, δ)` be a Chow situation, let
```
X' --f--> X
|         |
v         v
Y' --g--> Y
```
be a cartesian square of schemes locally of finite type over `S` with `g` proper, realized by
the fibre product `X' = X ×_Y Y'` with `f = pullback.fst`, let `r ≥ 0` and `e ∈ ℤ`, let `α` be a
family of `r`-cycles on the fibres of `X/Y` and let `β' ∈ Z_e(Y')`. Then

`f_*(g^*α ∩ β') = α ∩ g_*β'`   in   `Z_{r + e}(X)`,

where `∩` is the action `Stacks.Chow.cap` and `g^*α` is the base change
`Stacks.Chow.baseChangeFamily` of the family. -/
@[stacks 0H6B]
theorem properPushforward_cap_baseChangeFamily (C : ChowSituation.{u}) {X Y Y' : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (p : X ⟶ Y) [LocallyOfFiniteType p]
    (g : Y' ⟶ Y) [IsProper g] (hp : p ≫ sY = sX) (hg : g ≫ sY = sY') (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles p r) (β' : CycleGroup C sY' e) :
    properPushforward C (pullback.snd p g ≫ sY') sX (pullback.fst p g)
        (pullbackFst_comp_eq_of_base g hp hg) ((r : ℤ) + e)
        (cap C sY' (pullback.snd p g) (baseChangeFamily p g r α) β') =
      hp ▸ cap C sY p α (properPushforward C sY' sY g hg e β') := by
  classical
  subst hp
  subst hg
  apply properPushforward_cap_eq_of_cycleComponents C sY p g r e α β'
  intro y
  by_cases hy : relativeDimension C.dimensionFunction sY (g y) = e
  · by_cases hβ : β'.1 y = 0
    · have hc : cycleComponent C (g ≫ sY) β' y = 0 := by
        apply Subtype.ext
        ext z
        simp [cycleComponent_apply, hβ]
      rw [hc, cap_zero_right, properPushforward_zero, properPushforward_zero, cap_zero_right]
    · have hdim := relativeDimension_eq_of_cycleGroup_apply_ne_zero C (g ≫ sY) β' y hβ
      have hfinite := finiteDimensional_residueField_of_relativeDimension_eq
        C.dimensionFunction sY g y (hdim.trans hy.symm)
      apply Subtype.ext
      ext x
      by_cases hx : p x = g y
      · let q := (p.fiberHomeo (g y)).symm ⟨x, hx⟩
        have hq : p.fiberι (g y) q = x := p.fiberι_fiberHomeo_symm (g y) ⟨x, hx⟩
        let m := restrictedFiberMap p (pullback.snd p g) (pullback.fst p g) g
          pullback.condition y
        have : IsFinite m := restrictedFiberMap_isFinite p g y hfinite
        have : Flat m := restrictedFiberMap_flat p g y
        have : LocallyOfFiniteType (p.fiberToSpecResidueField (g y)) :=
          inferInstanceAs (LocallyOfFiniteType (pullback.snd p (Y.fromSpecResidueField (g y))))
        let α' := baseChangeFamily p g r α
        let γ := cap C (g ≫ sY) (pullback.snd p g) α' (cycleComponent C (g ≫ sY) β' y)
        let w (z : ↥(pullback p g : Scheme.{u})) :=
          γ.1 z * ((pullback.fst p g).residueDegree z : ℤ)
        have hzero (z : ↥(pullback p g : Scheme.{u})) (hz : (pullback.snd p g) z ≠ y) :
            γ.1 z = 0 := by
          simp [γ, cap_apply, capCoeff, cycleComponent_apply, hz]
        have hweight (z : ↥(pullback p g : Scheme.{u})) :
            γ.1 z * (if relativeDimension C.dimensionFunction (pullback.snd p g ≫ g ≫ sY) z =
                relativeDimension C.dimensionFunction (p ≫ sY) ((pullback.fst p g) z)
              then ((pullback.fst p g).residueDegree z : ℤ) else 0) = w z := by
          by_cases hz : γ.1 z = 0
          · simp [w, hz]
          · obtain ⟨-, h₁, h₂⟩ :=
              snd_eq_and_relativeDimension_of_cap_cycleComponent_ne_zero C sY p g r e α β' y z hz
            rw [h₁, h₂, hy, ite_eq_left rfl]
        have hsum := finsum_baseChangeFamily_residueDegree p g r α y hfinite q
        have hleft : (properPushforward C (pullback.snd p g ≫ g ≫ sY) (p ≫ sY)
              (pullback.fst p g) (pullbackFst_comp_eq g rfl) ((r : ℤ) + e) γ).1 x =
            β'.1 y * ((g.residueDegree y : ℤ) * (α (g y)).1 q) := by
          rw [properPushforward_apply]
          simp_rw [hweight]
          calc
            (∑ᶠ z ∈ (pullback.fst p g) ⁻¹' {x}, w z) =
                ∑ᶠ z ∈ (pullback.fst p g) ⁻¹' {x} ∩ (pullback.snd p g) ⁻¹' {y}, w z := by
              rw [finsum_mem_def, finsum_mem_def]
              apply finsum_congr
              intro z
              by_cases hz : (pullback.snd p g) z = y
              · simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage,
                  Set.mem_singleton_iff, hz, and_true]
              · have hwz : w z = 0 := by simp [w, hzero z hz]
                simp [Set.indicator_apply, hwz]
            _ = ∑ᶠ z ∈ m ⁻¹' {q}, w ((pullback.snd p g).fiberι y z) := by
              simpa only [hq] using (finsum_restrictedFiberMap_eq p g y q w).symm
            _ = β'.1 y * (∑ᶠ z ∈ m ⁻¹' {q}, (α' y).1 z * (m.residueDegree z : ℤ)) := by
              rw [mul_finsum_mem]
              apply finsum_mem_congr rfl
              intro z _
              have hz : (pullback.snd p g) ((pullback.snd p g).fiberι y z) = y :=
                ((pullback.snd p g).fiberHomeo y z).2
              have hfam := familyOfCycles_apply_of_fiberι (pullback.snd p g) α' y z
                ((pullback.snd p g).fiberι y z) rfl
              change _ * _ = _
              dsimp only [w]
              rw [cap_apply]
              unfold capCoeff
              rw [← hfam, cycleComponent_apply, ite_eq_left hz, ← restrictedFiberMap_residueDegree]
              ring
            _ = β'.1 y * ((g.residueDegree y : ℤ) * (α (g y)).1 q) := by rw [hsum]
        have hright : (properPushforward C (g ≫ sY) sY g rfl e
              (cycleComponent C (g ≫ sY) β' y)).1 (p x) =
            β'.1 y * (g.residueDegree y : ℤ) := by
          rw [properPushforward_apply, finsum_mem_def]
          rw [finsum_eq_single _ y (by
            intro z hz
            simp [Set.indicator_apply, cycleComponent_apply, hz])]
          simp [cycleComponent_apply, hx, hdim, hy]
        change (properPushforward C _ _ _ _ _ γ).1 x = _
        rw [hleft, cap_apply]
        unfold capCoeff
        rw [hright, ← familyOfCycles_apply_of_fiberι p α (g y) q x hq]
        ring
      · have hright : (properPushforward C (g ≫ sY) sY g rfl e
            (cycleComponent C (g ≫ sY) β' y)).1 (p x) = 0 := by
          rw [properPushforward_apply]
          apply finsum_mem_eq_zero_of_forall_eq_zero
          intro z hz
          have hzy : z ≠ y := by
            intro hzy
            subst z
            exact hx hz.symm
          simp [cycleComponent_apply, hzy]
        rw [cap_apply]
        unfold capCoeff
        rw [hright, zero_mul, properPushforward_apply]
        apply finsum_mem_eq_zero_of_forall_eq_zero
        intro z hz
        have hzy : (pullback.snd p g) z ≠ y := by
          intro hzy
          have hzx : (pullback.fst p g) z = x := hz
          exact hx (by rw [← hzx, apply_fst_eq_apply_snd, hzy])
        simp [cap_apply, capCoeff, cycleComponent_apply, hzy]
  · rw [properPushforward_cap_cycleComponent_eq_zero C sY p g r e α β' y hy,
      properPushforward_cycleComponent_eq_zero C sY g e β' y hy]
    exact ((capHom C sY p r e α).map_zero).symm

end Stacks.Chow

end
