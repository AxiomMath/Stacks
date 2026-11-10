module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass
public import StacksCore.Tactic.StacksAttribute

/-!
# Intersecting with the Chern classes of a finite locally free module

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `ℰ` be a finite locally free `𝒪_X`-module of rank `r`. Stacks 02U5 defines, for
every `k` and every `0 ≤ j ≤ r`, an additive cap product

  `Z_k(X) ⟶ A_{k-j}(X)`,  `α ↦ c_j(ℰ) ∩ α`,

by prescribing it on integral components: an integral closed subscheme `W ⊆ X` of
delta-dimension `k` is sent to the pushforward to `X` of `c_j(ℰ|_W) ∩ [W]`, the class of
Stacks 02U0, and the rule is extended coefficientwise over an arbitrary locally finite
presentation of a `k`-cycle. This file is that construction.

The extension is the same passage that `Stacks.Chow.firstChernClassCap` performs for the first
Chern class of an invertible module, except that the `j`-th Chern class lowers the
delta-dimension by `j` rather than by one; the first section of this file is the rule-extension
machinery at an arbitrary drop in degree.

## Main definitions

* `Stacks.Chow.cycleGroupOfEq` — a `d`-cycle read as an `e`-cycle when `d = e`.
* `Stacks.Chow.GradedIntegralComponentRule` — a rule on integral closed subschemes of
  delta-dimension `d` valued in `e`-cycles, and
  `Stacks.Chow.GradedIntegralComponentRule.extendChow` its coefficientwise extension
  `Z_d(X) ⟶ A_e(Y)`.
* `Stacks.Chow.ChernClassCycleRule` — the datum of Stacks 02U0: a cycle representing
  `c_j(F) ∩ [T]` on every integral `T` of delta-dimension `d`, for every finite locally free `F`
  of rank `r` on `T` and every `0 ≤ j ≤ r`.
* `Stacks.Chow.chernClassComponentCycle` — the cycle on `X` attached to an integral component.
* `Stacks.Chow.IsChernClassCap` — the locally finite component formula characterising the cap
  product.
* `Stacks.Chow.chernClassCapConstruction`, `Stacks.Chow.chernClassCap` — the cap product, with
  and without that formula.
* `Stacks.Chow.firstChernComponentCycleRuleOfRank` — the datum of Stacks 02U0 at `j = 1`, read as
  a `Stacks.Chow.FirstChernComponentCycleRule`.

## Main results

* `Stacks.Chow.chernClassCap_integral_cycle` — clause (1) of Stacks 02U5, the value on the
  fundamental cycle of a single integral closed subscheme.
* `Stacks.Chow.chernClassCap_finsum` — clause (2), the locally finite component formula.

## Implementation notes

### The Chern classes of Stacks 02U0 are an explicit parameter, and are cycle-valued

The component datum of Stacks 02U5 is `c_j(ℰ|_W) ∩ [W]`, which is Stacks 02U0. Every declaration
below takes the component classes as an explicit argument `chern`, a
`Stacks.Chow.ChernClassCycleRule`, so the construction is the parametric form of the definition and
no Stacks attribute sits here. The operation of Stacks 02U5 itself — at the datum of the classes of
Stacks 02U0, which
`StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesOfRank`
reads off the projective space bundle formula — is
`Stacks.Chow.GenuineChern.chernCapOnCycles` of
`StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCycles`, registered there with its two
clauses.

The parameter is *cycle*-valued rather than Chow-class valued, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass`: the extension of the rule over a locally
finite presentation is an infinite sum of cycles, which has no meaning in a Chow group. Clause
(1) is therefore proved here at the level of cycles, as it is for Stacks 02SO; its form on Chow
groups, through the proper pushforward of Stacks 0GU8, is
`Stacks.Chow.GenuineChern.chernCapOnCycles_integral_cycle`.

### Why the rule structure is restated with two degrees

`Stacks.Chow.IntegralComponentRule` ties the degree of the values to one less than the
delta-dimension of the subschemes the rule is given on, which is right for a first Chern class
and wrong for a `j`-th one. `Stacks.Chow.GradedIntegralComponentRule` is the same structure with
the two degrees independent; the former is the case `e = d - 1`.

### The rank hypothesis

`Stacks.Chow.PullbackPreservesRank` is the only hypothesis the module `ℰ` carries, as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Basic`: no declaration below also takes
`[AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank ℰ r]`. That is a generalization and
not a weakening, and it costs a caller nothing, since
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback` proves it for every finite locally free
module of rank `r`.

### What is not here

Stacks 02U7, the invariance of the cap product under rational equivalence, is not proved, so
nothing below descends to a homomorphism `A_k(X) ⟶ A_{k-j}(X)` and nothing below inhabits
`Stacks.Chow.HigherChernCapRule`, which is `chernClassCapOnChow` of Stacks 0B7G.

## References

* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02U7](https://stacks.math.columbia.edu/tag/02U7)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transporting a cycle along an equality of degrees -/

/-- A `d`-cycle is an `e`-cycle whenever `d = e`. -/
def cycleGroupOfEq {C : ChowSituation.{u}} {Y : Scheme.{u}} {q : Y ⟶ C.S}
    [LocallyOfFiniteType q] {d e : ℤ} (h : d = e) (α : CycleGroup C q d) : CycleGroup C q e :=
  ⟨α.1, h ▸ α.2⟩

/-- Reading a cycle in another degree does not change its coefficients. -/
@[simp]
theorem coe_cycleGroupOfEq {C : ChowSituation.{u}} {Y : Scheme.{u}} {q : Y ⟶ C.S}
    [LocallyOfFiniteType q] {d e : ℤ} (h : d = e) (α : CycleGroup C q d) :
    (cycleGroupOfEq h α).1 = α.1 :=
  rfl

/-! ### Rules on integral components with a prescribed drop in delta-dimension -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g : Y ⟶ X) (d e : ℤ)

/-- A rule on integral components of delta-dimension `d`, along a morphism `g : Y ⟶ X`, valued
in `e`-cycles: to every integral closed subscheme `W ⊆ X` of delta-dimension `d` it assigns an
`e`-cycle on `Y` whose support lies over `W`. -/
structure GradedIntegralComponentRule where
  /-- The `e`-cycle on `Y` attached to an integral closed subscheme of delta-dimension `d`. -/
  cycle : ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
    schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt) → CycleGroup C q e
  /-- The cycle attached to `W` is supported over `W`. -/
  support_subset : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)),
    Function.support (cycle W hW hDim).1 ⊆ g.base ⁻¹' (W.support : Set X)

namespace GradedIntegralComponentRule

variable {C p q g d e} (R : GradedIntegralComponentRule C p q g d e)

/-- The rule extended by zero to every quasi-coherent ideal sheaf of `X`. -/
def totalize (W : X.IdealSheafData) : AlgebraicCycle Y ℤ :=
  open Classical in
  if h : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt) then
    (R.cycle W h.1 h.2).1
  else 0

/-- On an integral closed subscheme of delta-dimension `d` the totalized rule is the rule. -/
theorem totalize_eq (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)) :
    R.totalize W = (R.cycle W hW hDim).1 := by
  classical
  rw [totalize, dite_eq_left (⟨hW, hDim⟩ : IsIntegral W.subscheme ∧ _)]

/-- Every value of the totalized rule is an `e`-cycle. -/
theorem totalize_mem_cyclesOfDimension (W : X.IdealSheafData) :
    R.totalize W ∈ cyclesOfDimension C q e := by
  classical
  by_cases h : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)
  · rw [R.totalize_eq W h.1 h.2]
    exact (R.cycle W h.1 h.2).2
  · rw [totalize, dite_eq_right h]
    exact (cyclesOfDimension C q e).zero_mem

/-- The totalized rule is supported over the subscheme it is attached to. -/
theorem support_totalize_subset (W : X.IdealSheafData) :
    Function.support (R.totalize W) ⊆ g.base ⁻¹' (W.support : Set X) := by
  classical
  by_cases h : IsIntegral W.subscheme ∧
      schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)
  · rw [R.totalize_eq W h.1 h.2]
    exact R.support_subset W h.1 h.2
  · rw [totalize, dite_eq_right h]
    simp

/-- A graded rule on integral components, read as a rule on points of `X`. -/
def toComponentRule : ComponentRule g.base where
  cycle x := R.totalize (integralComponentAt x)
  mem_closure_of_apply_ne_zero x y hy := by
    have h := R.support_totalize_subset (integralComponentAt x) (by exact hy)
    rwa [Set.mem_preimage, coe_support_integralComponentAt] at h

/-- The cycle the induced rule on points attaches to the generic point of an integral closed
subscheme of delta-dimension `d` is the cycle the original rule attaches to it. -/
theorem toComponentRule_cycle_genericPointOf (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)) :
    R.toComponentRule.cycle (genericPointOf W hW) = (R.cycle W hW hDim).1 := by
  change R.totalize (integralComponentAt (genericPointOf W hW)) = _
  rw [integralComponentAt_genericPointOf W hW, R.totalize_eq W hW hDim]

/-- The homomorphism `Z_d(X) → Z_e(Y)` extending a graded rule on integral components
coefficientwise. -/
def extendCycleGroup : CycleGroup C p d →+ CycleGroup C q e where
  toFun α := ⟨R.toComponentRule.extend g.continuous α.1, by
    rw [mem_cyclesOfDimension_iff_forall_point]
    intro y hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1
      (R.toComponentRule.support_extend_subset g.continuous α.1 (by exact hy))
    exact (mem_cyclesOfDimension_iff_forall_point C q e _).1
      (R.totalize_mem_cyclesOfDimension (integralComponentAt x)) y (by exact hx)⟩
  map_zero' := Subtype.ext (map_zero (R.toComponentRule.extend g.continuous))
  map_add' α β := Subtype.ext (map_add (R.toComponentRule.extend g.continuous) α.1 β.1)

/-- The coefficient of `R.extendCycleGroup α` at `y` is that of the coefficientwise extension of
the induced rule on points. -/
@[simp]
theorem extendCycleGroup_apply (α : CycleGroup C p d) (y : Y) :
    (R.extendCycleGroup α).1 y = R.toComponentRule.extend g.continuous α.1 y := rfl

/-- The homomorphism `Z_d(X) → A_e(Y)` to the Chow group extending a graded rule on integral
components coefficientwise. -/
def extendChow : CycleGroup C p d →+ chowGroup C q e :=
  (QuotientAddGroup.mk' (rationalEquivalences C q e)).comp R.extendCycleGroup

/-- `R.extendChow α` is the Chow class of the cycle `R.extendCycleGroup α`. -/
@[simp]
theorem extendChow_apply (α : CycleGroup C p d) :
    R.extendChow α = QuotientAddGroup.mk (R.extendCycleGroup α) := rfl

/-- **The defining formula.** On a locally finite presentation `α = ∑ n_j [W_j]` of a `d`-cycle by
integral closed subschemes of delta-dimension `d`, the extension of a graded rule on integral
components is the locally finite sum of the cycles the rule attaches to the `W_j`, weighted by
the coefficients `n_j`. -/
theorem extendCycleGroup_apply_of_presentation {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = (d : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p d)
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι d).1 x) (y : Y) :
    (R.extendCycleGroup α).1 y = ∑ᶠ j : J, n j * (R.cycle (W j) (hW j) (hDim j)).1 y := by
  have hclosure : (fun j ↦ closure {genericPointOf (W j) (hW j)}) =
      fun j ↦ ((W j).support : Set X) :=
    funext fun j ↦ (support_eq_closure_genericPointOf (W j) (hW j)).symm
  have hσ : LocallyFinite fun j ↦ closure {genericPointOf (W j) (hW j)} := by
    rwa [hclosure]
  rw [extendCycleGroup_apply,
    R.toComponentRule.extend_apply_of_presentation g.continuous
      (fun j ↦ genericPointOf (W j) (hW j)) n
      (fun j x ↦ (cycleAssociatedToClosedSubscheme C p (W j).subschemeι d).1 x)
      (fun j x hx ↦ by
        by_contra hne
        exact hx (cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p (W j) (hW j)
          d hne))
      (fun j ↦ cycleAssociatedToClosedSubscheme_integral_apply C p (W j) (hW j) (hDim j))
      hσ α.1 hα y]
  exact finsum_congr fun j ↦ by
    rw [R.toComponentRule_cycle_genericPointOf (W j) (hW j) (hDim j)]

/-- The value of the extension of a graded rule on integral components on the fundamental cycle
of a single integral closed subscheme of delta-dimension `d` is the cycle the rule attaches to
it. -/
theorem extendCycleGroup_cycleAssociatedToClosedSubscheme (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (d : EInt)) :
    R.extendCycleGroup (cycleAssociatedToClosedSubscheme C p W.subschemeι d) =
      R.cycle W hW hDim := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [R.extendCycleGroup_apply_of_presentation (fun _ : PUnit.{u + 1} ↦ W) (fun _ ↦ hW)
    (fun _ ↦ hDim) (fun _ ↦ ⟨Set.univ, Filter.univ_mem, Set.toFinite _⟩) (fun _ ↦ 1) _
    (fun x ↦ by simp [finsum_unique]) y]
  simp [finsum_unique]

end GradedIntegralComponentRule

/-! ### The Chern class component datum of Stacks 02U0 -/

/-- **Stacks 02U0 at the level of cycles.** For every integral scheme `T` locally of finite type
over the base, of delta-dimension `d`, every finite locally free module `F` of rank `r` on it and
every `0 ≤ j ≤ r`, a `(d - j)`-cycle on `T` representing `c_j(F) ∩ [T]`. -/
abbrev ChernClassCycleRule (C : ChowSituation.{u}) (r : ℕ) : Type (u + 1) :=
  ∀ {T : Scheme.{u}} (pT : T ⟶ C.S) [LocallyOfFiniteType pT], IsIntegral T →
    ∀ (F : T.Modules)
      [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (d : ℤ),
      schemeDeltaDimension C pT = (d : EInt) → ∀ j : Fin (r + 1),
      CycleGroup C pT (d - (j : ℤ))

/-! ### Intersecting with the `j`-th Chern class -/

variable {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (E : X.Modules) (r : ℕ)
  (hrank : PullbackPreservesRank E r) (k : ℤ) (j : Fin (r + 1))
  (chern : ChernClassCycleRule C r)

/-- The cycle on an integral closed subscheme `W ⊆ X` of delta-dimension `k` representing
`c_j(ℰ|_W) ∩ [W]`, read off the datum of Stacks 02U0 at the restriction `ℰ|_W`. -/
def chernClassComponentCycleOn (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    CycleGroup C (W.subschemeι ≫ p) (k - (j : ℤ)) :=
  have _hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback W.subschemeι).obj E) r := hrank W.subschemeι
  chern (W.subschemeι ≫ p) hW ((Scheme.Modules.pullback W.subschemeι).obj E) k hDim j

/-- **Stacks 02U5 (1).** The cycle on `X` attached to an integral closed subscheme `W` of
delta-dimension `k`: the pushforward along `W ⟶ X` of a cycle representing
`c_j(ℰ|_W) ∩ [W]`. -/
def chernClassComponentCycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    CycleGroup C p (k - (j : ℤ)) :=
  properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl (k - (j : ℤ))
    (chernClassComponentCycleOn C p E r hrank k j chern W hW hDim)

/-- The component cycle of `W` is supported on `W`: a proper pushforward is supported on the
image of the morphism, and the image of the closed immersion of `W` is the support of `W`. -/
theorem support_chernClassComponentCycle_subset (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    Function.support (chernClassComponentCycle C p E r hrank k j chern W hW hDim).1 ⊆
      (𝟙 X : X ⟶ X).base ⁻¹' (W.support : Set X) := by
  refine (support_properPushforward_subset C (W.subschemeι ≫ p) p W.subschemeι rfl
    (k - (j : ℤ)) _).trans ?_
  rw [W.range_subschemeι]
  exact fun _ hx ↦ hx

/-- **Stacks 02U5.** The component rule of the `j`-th Chern class cap product, attaching to an
integral closed subscheme `W` of delta-dimension `k` the cycle
`Stacks.Chow.chernClassComponentCycle`. -/
def chernClassCapRule : GradedIntegralComponentRule C p p (𝟙 X) k (k - (j : ℤ)) where
  cycle := chernClassComponentCycle C p E r hrank k j chern
  support_subset := support_chernClassComponentCycle_subset C p E r hrank k j chern

/-- **Stacks 02U5 (2).** The component rule extended coefficientwise to every locally finite
presentation of a `k`-cycle. -/
def IsChernClassCap (F : CycleGroup C p k →+ chowGroup C p (k - (j : ℤ))) : Prop :=
  ∀ {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ t, IsIntegral (W t).subscheme)
    (hDim : ∀ t, schemeDeltaDimension C ((W t).subschemeι ≫ p) = (k : EInt))
    (_hLocal : LocallyFinite fun t ↦ ((W t).support : Set X))
    (n : J → ℤ) (α : CycleGroup C p k),
    (∀ x : X, α.1 x = ∑ᶠ t : J, n t *
      (cycleAssociatedToClosedSubscheme C p (W t).subschemeι k).1 x) →
    ∃ β : CycleGroup C p (k - (j : ℤ)),
      F α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ t : J, n t *
        (chernClassComponentCycle C p E r hrank k j chern (W t) (hW t) (hDim t)).1 x

/-- **Stacks 02U5.** Construction of intersection with the `j`-th Chern class, together with the
two clauses of the definition. -/
def chernClassCapConstruction :
    { F : CycleGroup C p k →+ chowGroup C p (k - (j : ℤ)) //
      IsChernClassCap C p E r hrank k j chern F } :=
  ⟨(chernClassCapRule C p E r hrank k j chern).extendChow, by
    intro J W hW hDim hLocal n α hα
    refine ⟨(chernClassCapRule C p E r hrank k j chern).extendCycleGroup α, rfl, fun x ↦ ?_⟩
    exact (chernClassCapRule C p E r hrank k j chern).extendCycleGroup_apply_of_presentation
      W hW hDim hLocal n α hα x⟩

/-- **Stacks 02U5.** Intersection with the `j`-th Chern class of a finite locally free module of
rank `r`, as a homomorphism `Z_k(X) ⟶ A_{k-j}(X)`, at the datum `chern` of Stacks 02U0. -/
def chernClassCap : CycleGroup C p k →+ chowGroup C p (k - (j : ℤ)) :=
  (chernClassCapConstruction C p E r hrank k j chern).val

/-- **Stacks 02U5 (1).** On the fundamental cycle of a single integral closed subscheme of
delta-dimension `k` the cap product is the class of the pushforward to `X` of
`c_j(ℰ|_W) ∩ [W]`. -/
theorem chernClassCap_integral_cycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = (k : EInt)) :
    chernClassCap C p E r hrank k j chern
        (cycleAssociatedToClosedSubscheme C p W.subschemeι k) =
      QuotientAddGroup.mk
        (chernClassComponentCycle C p E r hrank k j chern W hW hDim) := by
  change QuotientAddGroup.mk
    ((chernClassCapRule C p E r hrank k j chern).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p W.subschemeι k)) = _
  exact congrArg QuotientAddGroup.mk
    ((chernClassCapRule C p E r hrank k j chern).extendCycleGroup_cycleAssociatedToClosedSubscheme
      W hW hDim)

/-- **Stacks 02U5 (2).** On a presentation `α = ∑ n_t [W_t]` of a `k`-cycle by integral closed
subschemes of delta-dimension `k`, the cap product is the class of
`∑ n_t (c_j(ℰ) ∩ [W_t])`. -/
theorem chernClassCap_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ t, IsIntegral (W t).subscheme)
    (hDim : ∀ t, schemeDeltaDimension C ((W t).subschemeι ≫ p) = (k : EInt))
    (hLocal : LocallyFinite fun t ↦ ((W t).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ t : J, n t *
      (cycleAssociatedToClosedSubscheme C p (W t).subschemeι k).1 x) :
    ∃ β : CycleGroup C p (k - (j : ℤ)),
      chernClassCap C p E r hrank k j chern α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ t : J, n t *
        (chernClassComponentCycle C p E r hrank k j chern (W t) (hW t) (hDim t)).1 x :=
  (chernClassCapConstruction C p E r hrank k j chern).2 W hW hDim hLocal n α hα

/-! ### The first Chern class of a module of rank `r` -/

/-- The datum of Stacks 02U0 at `j = 1` is a first Chern class component rule in the sense of
`Stacks.Chow.FirstChernComponentCycleRule`, for a finite locally free module of rank `r ≥ 1`. -/
def firstChernComponentCycleRuleOfRank (hr : 0 < r) (m : ℤ) :
    FirstChernComponentCycleRule C p m := fun W hW hDim =>
  cycleGroupOfEq (by simp)
    (chernClassComponentCycleOn C p E r hrank (m + 1) ⟨1, by omega⟩ chern W hW hDim)

end Stacks.Chow

end
