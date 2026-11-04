module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardDimensionDrop
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Triviality

/-!
# The Gysin map on cycles commutes with proper pushforward

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `X'` be
schemes locally of finite type over `S`, let `f : X' ⟶ X` be proper over `S`, and let
`(L, s, i : D ⟶ X)` be a triple as in Stacks 02T8: `L` an invertible module on `X`, `s` a global
section of `L` and `i` the closed immersion of the zero scheme `D = Z(s)`. Setting `L' = f^*L`,
`s' = f^*s` and `D' = Z(s')` gives the cartesian square of Stacks 0B6Y

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

with `g` the morphism `Stacks.Divisors.zeroSchemePullbackMap`. **Stacks 0H6D** is the identity

  `i^* f_* α' = g_* (i')^* α'`  in  `Z_k(D)`,  for `α' ∈ Z_{k+1}(X')`,

for the Gysin maps *on cycles* of Stacks 0B6Z, which exist because `L|_D ≅ 𝒪_D`.

The identity is an equality of cycles, not of classes. This is what distinguishes it from
Stacks 02TA, whose Gysin map takes values in the Chow group `A_k(D)` and for which the
corresponding cycles differ by a rational equivalence
(`Stacks.Chow.rationallyEquivalent_gysinRule_extendCycleGroup_properPushforward`). The gain comes
from the second branch of the source's proof: on an integral component contained in the divisor
the Gysin map on cycles is *zero by construction*, so where Stacks 02TA has to compare two
pushed-forward first Chern classes up to rational equivalence, here both sides vanish outright.

## Main definitions

* `Stacks.Chow.IntegralComponentRule.cycleAt` — the cycle a rule on integral components attaches
  to a *point*, namely the one it attaches to the integral closed subscheme that point is the
  generic point of, extended by zero in the wrong delta-dimension. This is the point-indexed form
  `Stacks.Chow.gysinComponentCycleAt` takes for the Gysin rule of Stacks 02T8, stated once for
  every rule.

## Main results

* `Stacks.Chow.properPushforward_extendCycleGroup_of_compatibleAt` — the assembly step: two rules
  on integral components whose point-indexed cycles are compatible along `f` have
  `f`-compatible extensions to all cycles.
* `Stacks.Chow.properPushforward_gysinCycleMapRule_cycleAt` — **the integral-component case of
  Stacks 0H6D**, proved outright: no hypothesis beyond the properness of `f`.
* `Stacks.Chow.properPushforward_gysinCycleMap` — **Stacks 0H6D**, the identity
  `i^* f_* α' = g_* (i')^* α'` of `k`-cycles on `D`.

## Implementation notes

### Why the integral-component case is a theorem here and a hypothesis in Stacks 02TA

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward` carries the integral-component case
of Stacks 02TA as the hypothesis `Stacks.Chow.GysinCompatibleWithPushforward`, and necessarily so:
the Gysin map there is built from an arbitrary `Stacks.Chow.FirstChernComponentClassRule` on each
of `X` and `X'`, and two unrelated rules have no reason to be compatible along `f`. The Gysin map
on cycles of Stacks 0B6Z takes no such parameter — its value on a component inside the divisor is
zero — so nothing is left to assume, and the three branches of the source's case distinction are
all available in this repository:

* the component is *not* inside `D'` and `f` preserves its delta-dimension: this is
  `Stacks.Chow.properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme`, the
  identity `g_*[W' ∩ D']_k = w(x') · [W ∩ D]_k` of cycles, which is where the source invokes
  Chow Homology, Lemma 42.26.3;
* the component is not inside `D'` and the delta-dimension drops: the pushforward weight is zero
  and so is the pushed-forward component cycle, by
  `Stacks.Chow.properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne`;
* the component *is* inside `D'`: then its image is inside `D`
  (`Stacks.Chow.pullbackZeroScheme_le_integralComponentAt_iff`, which is Stacks 0B6Y), and both
  component cycles are zero by the construction of Stacks 0B6Z. This is the source's "both sides
  are zero by construction".

The second branch is stated in the source's vocabulary, for the Gysin rule of Stacks 02T8 with an
arbitrary first-Chern component rule. Off the divisor that rule does not enter, which is
`Stacks.Chow.gysinCycleMapRule_cycleAt_eq_gysinComponentCycleAt_of_not_le`, so it is reused rather
than reproved.

### The triviality hypothesis on the pullback is derived, not assumed

Stacks 0H6D assumes only `L|_D ≅ 𝒪_D`. The Gysin map on cycles of `(L', s')` needs the
corresponding triviality on `D'`, and that is a consequence, not a further hypothesis: `D'` is the
inverse image of `D` by Stacks 0B6Y, so `L'|_{D'}` is a pullback of `L|_D`. The derivation is
`Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections`, and the statement below
supplies it rather than quantifying over it.

### The assembly step is stated for arbitrary rules

`Stacks.Chow.properPushforward_extendCycleGroup_of_compatibleAt` is the proof of
`Stacks.Chow.properPushforward_gysinRule_extendCycleGroup` with the Gysin rule of Stacks 02T8
replaced by an arbitrary pair of rules on integral components: nothing in that argument is about
divisors, only that both sides are locally finite sums over the integral components of `α'`,
reindexed over the fibres of `f` and of `g` by
`Stacks.Chow.ComponentRule.extendCoeff_map_apply` and
`Stacks.Chow.ComponentRule.map_extendCycle_apply`. A dedup pass should rewire
`Stacks.Chow.properPushforward_gysinRule_extendCycleGroup` through it; that is a change to
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward` and is not made here.

## References

* [Stacks Project, Tag 0H6D](https://stacks.math.columbia.edu/tag/0H6D)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
* [Stacks Project, Tag 02TA](https://stacks.math.columbia.edu/tag/02TA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### A rule on integral components, read at a point -/

namespace IntegralComponentRule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p]
  {q : Y ⟶ C.S} [LocallyOfFiniteType q] {g : Y ⟶ X} {k : ℤ}
  (R : IntegralComponentRule C p q g k)

/-- The cycle a rule on integral components attaches to a *point* of `X`: the cycle it attaches to
the integral closed subscheme `closure {x}`, extended by zero when that subscheme does not have
delta-dimension `k + 1`.

For the Gysin rule of Stacks 02T8 this is `Stacks.Chow.gysinComponentCycleAt`, with which it
agrees definitionally; it is the form in which the coefficientwise extension of a rule is
written. -/
def cycleAt (x : X) : CycleGroup C q k :=
  ⟨R.totalize (integralComponentAt x), R.totalize_mem_cyclesOfDimension _⟩

/-- At a point whose integral component has delta-dimension `k + 1` the point-indexed cycle is the
cycle the rule attaches to that component. -/
theorem cycleAt_eq_cycle (x : X) (hW : IsIntegral (integralComponentAt x).subscheme)
    (hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) :
    R.cycleAt x = R.cycle (integralComponentAt x) hW hDim :=
  Subtype.ext (R.totalize_eq _ hW hDim)

/-- Outside delta-dimension `k + 1` the point-indexed cycle is zero: that is how the rule is
extended off the components it is defined on. -/
theorem cycleAt_eq_zero (x : X)
    (h : ¬ (IsIntegral (integralComponentAt x).subscheme ∧
      schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt))) :
    R.cycleAt x = 0 := by
  classical
  refine Subtype.ext ?_
  show R.totalize (integralComponentAt x) = 0
  rw [totalize, dite_eq_right h]

/-- To compute the point-indexed cycle it suffices to know the cycle the rule attaches to the
component of `x` when it is defined, and that the answer is zero when it is not. -/
private theorem cycleAt_eq_of_cycle_eq (x : X) (c : CycleGroup C q k)
    (h : ∀ (hW : IsIntegral (integralComponentAt x).subscheme)
      (hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt)), R.cycle (integralComponentAt x) hW hDim = c)
    (h0 : ¬ (IsIntegral (integralComponentAt x).subscheme ∧
      schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt)) → c = 0) :
    R.cycleAt x = c := by
  by_cases hd : IsIntegral (integralComponentAt x).subscheme ∧
      schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)
  · rw [R.cycleAt_eq_cycle x hd.1 hd.2, h hd.1 hd.2]
  · rw [R.cycleAt_eq_zero x hd, h0 hd]

end IntegralComponentRule

/-! ### The assembly step, for an arbitrary pair of rules -/

section Assembly

variable (C : ChowSituation.{u}) {X X' Y Y' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (q : Y ⟶ C.S) [LocallyOfFiniteType q]
  (q' : Y' ⟶ C.S) [LocallyOfFiniteType q'] (i : Y ⟶ X) (i' : Y' ⟶ X') (k : ℤ)
  (R : IntegralComponentRule C p q i k) (R' : IntegralComponentRule C p' q' i' k)
  (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p') (g : Y' ⟶ Y) [IsProper g] (hg : g ≫ q = q')

/-- **The assembly step.** Two rules on integral components whose point-indexed cycles satisfy the
weighted compatibility along `f` have extensions to all cycles that commute with proper
pushforward.

Both sides are locally finite sums over the integral components of `α'`, and the proof matches
them term by term: `Stacks.Chow.ComponentRule.extendCoeff_map_apply` turns the left side into
`∑_{x'} α'(x') · w(x') · c(f x')` and `Stacks.Chow.ComponentRule.map_extendCycle_apply` turns the
right side into `∑_{x'} α'(x') · g_*(c'(x'))`, after which the hypothesis applies term by term.
Only the points carrying a nonzero coefficient of `α'` are compared, and those have relative
dimension `k + 1` because `α'` is a `(k+1)`-cycle. -/
theorem properPushforward_extendCycleGroup_of_compatibleAt
    (hcomp : ∀ x' : X', relativeDimension C.dimensionFunction p' x' = k + 1 → ∀ y : Y,
      (properPushforward C q' q g hg k (R'.cycleAt x')).1 y =
        pushforwardWeight C p' p f x' * (R.cycleAt (f.base x')).1 y)
    (α : CycleGroup C p' (k + 1)) :
    R.extendCycleGroup (properPushforward C p' p f hf (k + 1) α) =
      properPushforward C q' q g hg k (R'.extendCycleGroup α) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hcptf : IsCompact (f.base ⁻¹' {i.base y}) :=
    f.isProperMap.isCompact_preimage isCompact_singleton
  have hLHS : (R.extendCycleGroup (properPushforward C p' p f hf (k + 1) α)).1 y =
      ∑ᶠ x' : X', α.1 x' * pushforwardWeight C p' p f x' * (R.cycleAt (f.base x')).1 y := by
    rw [show (R.extendCycleGroup (properPushforward C p' p f hf (k + 1) α)).1 y =
      R.toComponentRule.extendCoeff
        (Function.locallyFinsupp.map f.base (pushforwardWeight C p' p f) f.isSpectralMap α.1)
        y from rfl,
      ComponentRule.extendCoeff_map_apply _ f.isSpectralMap f.isProperMap.isClosedMap _ _ y hcptf]
    exact finsum_congr fun _ ↦ rfl
  have hcptg : IsCompact (g.base ⁻¹' {y}) := g.isProperMap.isCompact_preimage isCompact_singleton
  have hRHS : (properPushforward C q' q g hg k (R'.extendCycleGroup α)).1 y =
      ∑ᶠ x' : X', α.1 x' * (properPushforward C q' q g hg k (R'.cycleAt x')).1 y := by
    rw [properPushforward_apply_eq_map,
      show (R'.extendCycleGroup α).1 =
        R'.toComponentRule.extendCycle i'.continuous α.1 from rfl,
      ComponentRule.map_extendCycle_apply _ _ _ _ _ hcptg]
    exact finsum_congr fun _ ↦ rfl
  rw [hLHS, hRHS]
  refine finsum_congr fun x' ↦ ?_
  by_cases hx : α.1 x' = 0
  · rw [hx, zero_mul, zero_mul, zero_mul]
  · rw [hcomp x' ((mem_cyclesOfDimension_iff_forall_point C p' (k + 1) α.1).1 α.2 x' hx) y]
    ring

end Assembly

/-! ### The Gysin rule on cycles, read at a point -/

section Component

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Stacks 0B6Z.** The point-indexed cycle of the Gysin rule on cycles vanishes at a point whose
integral component is contained in the zero scheme. This is the prescription of Stacks 0B6Z, and
it is the branch of Stacks 0H6D the source dispatches with "both sides are zero by
construction". -/
theorem gysinCycleMapRule_cycleAt_eq_zero_of_le (x : X)
    (h : zeroScheme X L s ≤ integralComponentAt x) :
    (gysinCycleMapRule C p k L s).cycleAt x = 0 :=
  IntegralComponentRule.cycleAt_eq_of_cycle_eq _ x 0
    (fun hW hDim ↦ gysinCycleMapComponent_of_le C p k L s (integralComponentAt x) hW hDim h)
    fun _ ↦ rfl

/-- **Off the divisor the Gysin rule on cycles is the Gysin rule of Stacks 02T8.** At a point whose
integral component is not contained in the zero scheme both rules take the fundamental cycle of
the scheme-theoretic intersection with the zero scheme, whatever first-Chern component rule the
rule of Stacks 02T8 is built from: that parameter governs only the contained components.

This is what lets the uncontained branches of Stacks 0H6D be taken from
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardUncontained` and
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforwardDimensionDrop` rather than
reproved. -/
theorem gysinCycleMapRule_cycleAt_eq_gysinComponentCycleAt_of_not_le
    (chern : FirstChernComponentClassRule C p k) (x : X)
    (h : ¬ zeroScheme X L s ≤ integralComponentAt x) :
    (gysinCycleMapRule C p k L s).cycleAt x = gysinComponentCycleAt C p k L s chern x :=
  IntegralComponentRule.cycleAt_eq_of_cycle_eq _ x _
    (fun hW hDim ↦
      (gysinCycleMapComponent_of_not_le C p k L s (integralComponentAt x) hW hDim h).trans
        ((gysinComponentCycle_of_not_le C p k L s chern (integralComponentAt x) hW hDim
          h).symm.trans ((gysinRule C p k L s chern).cycleAt_eq_cycle x hW hDim).symm))
    fun hd ↦ (gysinRule C p k L s chern).cycleAt_eq_zero x hd

/-- At a point of relative dimension `k + 1` whose integral component is not contained in the zero
scheme, the point-indexed cycle of the Gysin rule on cycles is the fundamental cycle of the
scheme-theoretic intersection of that component with the zero scheme. -/
theorem gysinCycleMapRule_cycleAt_of_not_le (x : X)
    (hx : relativeDimension C.dimensionFunction p x = k + 1)
    (h : ¬ zeroScheme X L s ≤ integralComponentAt x) :
    (gysinCycleMapRule C p k L s).cycleAt x =
      cycleAssociatedToClosedSubscheme C ((zeroScheme X L s).subschemeι ≫ p)
        ((integralComponentAt x).comap (zeroScheme X L s).subschemeι).subschemeι k := by
  rw [(gysinCycleMapRule C p k L s).cycleAt_eq_cycle x (isIntegral_integralComponentAt x)
      (schemeDeltaDimension_integralComponentAt_of_eq C p hx),
    show (gysinCycleMapRule C p k L s).cycle (integralComponentAt x)
        (isIntegral_integralComponentAt x)
        (schemeDeltaDimension_integralComponentAt_of_eq C p hx) =
      gysinCycleMapComponent C p k L s (integralComponentAt x) (isIntegral_integralComponentAt x)
        (schemeDeltaDimension_integralComponentAt_of_eq C p hx) from rfl]
  exact gysinCycleMapComponent_of_not_le C p k L s (integralComponentAt x)
    (isIntegral_integralComponentAt x) (schemeDeltaDimension_integralComponentAt_of_eq C p hx) h

end Component

/-! ### Stacks 0H6D -/

section Proper

variable (C : ChowSituation.{u}) {X X' : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (p' : X' ⟶ C.S) [LocallyOfFiniteType p'] (f : X' ⟶ X) [IsProper f] (hf : f ≫ p = p') (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **The integral-component case of Stacks 0H6D**, with no hypothesis beyond the properness of
`f`: for every point `x'` of `X'` of relative dimension `k + 1`, the pushforward along the
morphism `g` of Remark 0B6Y of the point-indexed Gysin cycle on `X'` is the point-indexed Gysin
cycle at the image point, weighted by `Stacks.Chow.pushforwardWeight`.

This is the first part of the source's proof, in its three cases. If the component of `x'` lies
inside `D'` then its image lies inside `D` (Stacks 0B6Y) and both cycles are zero by the
construction of Stacks 0B6Z. Otherwise the Gysin cycles are fundamental cycles of
scheme-theoretic intersections, and the identity is
`Stacks.Chow.properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme` when `f`
preserves the delta-dimension of the component, and the vanishing of both sides when it does
not. -/
theorem properPushforward_gysinCycleMapRule_cycleAt (x' : X')
    (hx' : relativeDimension C.dimensionFunction p' x' = k + 1)
    (y : (zeroScheme X L s).subscheme) :
    (properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        ((gysinCycleMapRule C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)).cycleAt x')).1 y =
      pushforwardWeight C p' p f x' *
        ((gysinCycleMapRule C p k L s).cycleAt (f.base x')).1 y := by
  by_cases hle : zeroScheme X L s ≤ integralComponentAt (f.base x')
  · -- The component lies inside the divisor: both sides are zero by construction.
    rw [gysinCycleMapRule_cycleAt_eq_zero_of_le C p' k _ _ x'
        ((pullbackZeroScheme_le_integralComponentAt_iff f L s x').2 hle),
      gysinCycleMapRule_cycleAt_eq_zero_of_le C p k L s (f.base x') hle]
    simp
  · have hle' : ¬ pullbackZeroScheme f L s ≤ integralComponentAt x' := fun h ↦
      hle ((pullbackZeroScheme_le_integralComponentAt_iff f L s x').1 h)
    by_cases hdim : relativeDimension C.dimensionFunction p (f.base x') = k + 1
    · -- Uncontained, delta-dimension preserved: Chow Homology, Lemma 42.26.3.
      rw [gysinCycleMapRule_cycleAt_of_not_le C p' k _ _ x' hx' hle',
        gysinCycleMapRule_cycleAt_of_not_le C p k L s (f.base x') hdim hle,
        properPushforward_zeroSchemePullbackMap_cycleAssociatedToClosedSubscheme C p p' f hf L s
          k x' hx' hdim hle]
      simp only [AddSubgroupClass.coe_zsmul, Function.locallyFinsuppWithin.coe_zsmul,
        Pi.smul_apply, smul_eq_mul]
    · -- Uncontained, delta-dimension drops: the weight and the pushforward both vanish.
      have hw : pushforwardWeight C p' p f x' = 0 :=
        pushforwardWeight_eq_zero C p' p f (x := x') (by rw [hx']; exact fun h ↦ hdim h.symm)
      rw [hw, zero_mul,
        gysinCycleMapRule_cycleAt_eq_gysinComponentCycleAt_of_not_le C p' k _ _
          (fun _ _ _ ↦ 0) x' hle',
        properPushforward_gysinComponentCycleAt_eq_zero_of_relativeDimension_ne C p p' k L s f hf
          (fun _ _ _ ↦ 0) (zeroSchemePullbackMap f L s)
          (zeroSchemePullbackMap_comp_subschemeι f L s)
          (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) x' hx' hdim hle']
      simp

/-- **Stacks 0H6D.** The Gysin map on cycles of Stacks 0B6Z commutes with proper pushforward:
in the cartesian square of Stacks 0B6Y

  `D' --i'--> X'`
  `|g          |f`
  `D  --i-->  X`

attached to a triple `(L, s, i : D ⟶ X)` whose invertible module restricts trivially to the zero
scheme `D = Z(s)`, one has `i^* f_* α' = g_* (i')^* α'` in `Z_k(D)` for every `α' ∈ Z_{k+1}(X')`.

The triviality of `L'|_{D'}` that the Gysin map on `X'` needs is not a hypothesis: it follows from
the triviality of `L|_D`, by
`Stacks.Divisors.isTrivial_pullback_zeroScheme_pullbackGlobalSections`. -/
@[stacks 0H6D]
theorem properPushforward_gysinCycleMap
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial (zeroScheme X L s).subscheme.sheaf.obj
      (zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (zeroScheme X L s).subschemeι).obj L))
    (α : CycleGroup C p' (k + 1)) :
    gysinCycleMap C p k L s htriv (properPushforward C p' p f hf (k + 1) α) =
      properPushforward C ((pullbackZeroScheme f L s).subschemeι ≫ p')
        ((zeroScheme X L s).subschemeι ≫ p) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf) k
        (gysinCycleMap C p' k ((Scheme.Modules.pullback f).obj L)
          (AlgebraicGeometry.pullbackGlobalSections f L s)
          (isTrivial_pullback_zeroScheme_pullbackGlobalSections f L s htriv) α) :=
  properPushforward_extendCycleGroup_of_compatibleAt C p p'
    ((zeroScheme X L s).subschemeι ≫ p) ((pullbackZeroScheme f L s).subschemeι ≫ p')
    (zeroScheme X L s).subschemeι (pullbackZeroScheme f L s).subschemeι k
    (gysinCycleMapRule C p k L s)
    (gysinCycleMapRule C p' k ((Scheme.Modules.pullback f).obj L)
      (AlgebraicGeometry.pullbackGlobalSections f L s))
    f hf (zeroSchemePullbackMap f L s)
    (zeroSchemePullbackMap_comp_structureMorphism f L s p p' hf)
    (properPushforward_gysinCycleMapRule_cycleAt C p p' f hf k L s) α

end Proper

end Stacks.Chow

end
