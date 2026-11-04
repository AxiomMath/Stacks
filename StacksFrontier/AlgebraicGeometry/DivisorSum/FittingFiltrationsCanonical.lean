module

public import StacksFrontier.AlgebraicGeometry.DivisorSum.FittingGradedPieces
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.FlatPullbackStalk.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction
public import StacksFrontier.AlgebraicGeometry.IdealPowerSmul.Functoriality
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleKernel
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleOpen
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule
public import StacksFrontier.RingTheory.Fitting.GlobalGradedPieces

/-!
# The endpoints, the local finiteness and the canonicity of 0ESU's two filtrations

`StacksFrontier.AlgebraicGeometry.DivisorSum.FittingFiltrations` defines the two filtrations
`AlgebraicGeometry.fittingIncr` and `AlgebraicGeometry.fittingDecr` of Stacks tag 0ESU as
subsheaves of `ℱ`, proves them monotone and identifies their sections on an affine open carrying
local equations `e_1, …, e_N` for the divisors. The source asserts three further things about
them, none of which was available:

```
0 = F⁰,        ℱ = F₁,        both filtrations are locally finite and canonical.
```

This file proves all of them, at the sheaf level and against the hypotheses that
`AlgebraicGeometry.exists_isAdmissibleBlowup_divisors_filtrations` already supplies — a locally
finite family of effective Cartier divisors together with the chart data — so they compose with
it without restating the blowup.

## Main results

* `AlgebraicGeometry.fittingIncr_zero_eq_bot`: **the increasing filtration starts at zero**,
  `F⁰ = 0`.
* `AlgebraicGeometry.fittingDecr_one_eq_top`: **the decreasing filtration starts at the whole
  module in degree one**, `F₁ = ℱ`.
* `AlgebraicGeometry.exists_isZero_pullback_cokernel_fittingIncr`: **the increasing filtration is
  locally exhaustive** — around every point there is an open `V` and an `N` beyond which the
  cokernel of `Fⁿ ⟶ ℱ` vanishes on `V`.
* `AlgebraicGeometry.exists_isZero_pullback_fittingDecr`: **the decreasing filtration is locally
  separated** — around every point there is an open `V` and an `N` beyond which `F_n` itself
  vanishes on `V`.
* `AlgebraicGeometry.rangeSubmodule_fittingIncr_comp` and
  `AlgebraicGeometry.rangeSubmodule_fittingDecr_comp`: **both filtrations are canonical** — every
  automorphism of `ℱ` carries each filtration term onto itself.

## Implementation notes

**The endpoints are affine-local, but the chart is not available on every affine open.** The two
anchors `F⁰ = 0` and `F₁ = ℱ` are read off the ring-level
`Stacks.FittingFiltration.incr_zero_eq_bot` and `Stacks.FittingFiltration.decr_one_eq_top`
through `AlgebraicGeometry.sectionsSubmodule_fittingIncr` and
`AlgebraicGeometry.sectionsSubmodule_fittingDecr`, which need the whole chart data: the local
equations, their being nonzerodivisors, and the product formula for the Fitting ideals. The chart
hypothesis provides that around every point, not on every affine open, and an equality of
subsheaves has to be checked over every open. The bridge is
`AlgebraicGeometry.exists_affineOpen_le_chart`: the chart data descends from an affine open to a
basic open of it, because the ideal sheaves restrict by
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen` and a nonzerodivisor stays one in
the localization. Since the basic opens of the charts form a basis of the topology, membership —
which is local in a subsheaf — can be decided there.

**Local finiteness needs only the equations.** Past the index `N` of a chart the tail product
`e_{n+1} ⋯ e_N` is empty, so `Fⁿ` is everything and `F_n` is zero on the chart; only the two
clauses `hlow` and `htop` of the chart data enter, and those restrict to *every* smaller affine
open by `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`. Vanishing of the restriction to an
open is then read on stalks:
`Stacks.SheafOfModules.subsingleton_stalk_cokernel_submodule_ι` for the cokernel of the
increasing filtration, and `AlgebraicGeometry.isZero_pullback_asModules_of_forall_obj_eq_bot`
below for the decreasing one.

**Canonicity is formal.** Neither filtration refers to a chart: the increasing one is an
ideal multiple and the decreasing one an annihilator, and both constructions are *functorial* in
the module. So an automorphism `e` of `ℱ` lifts to each filtration term, by
`AlgebraicGeometry.idealPowSmulMap` and `Stacks.SheafOfModules.annihilatorLift`, and the lift
commutes with the inclusions. That is exactly what
`AlgebraicGeometry.Scheme.Modules.rangeSubmodule_le_rangeSubmodule_of_comm` consumes, in both
directions once the lift of `e.inv` is used for the second. No chart, no divisor and no local
finiteness hypothesis is needed, which is the precise sense in which the filtrations are
canonical.

**The image of a subsheaf along an automorphism** is
`AlgebraicGeometry.Scheme.Modules.rangeSubmodule`, the library's sectionwise range of a
monomorphism; under the order isomorphism
`AlgebraicGeometry.Scheme.Modules.submoduleOrderIsoSubobject` it is the subobject
`Subobject.map e.hom`. No new transport is introduced.

## References

* [Stacks Project, Tag 0ESU](https://stacks.math.columbia.edu/tag/0ESU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Divisors Stacks.FittingFiltration
open Stacks.AlgebraicGeometry.AnnihilatorQcoh Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

/-- The extension of an ideal along a ring homomorphism is multiplicative over a finite product,
which is what carries the product formula for the Fitting ideals to a basic open. -/
theorem Ideal.map_finsetProd {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (s : Finset ℕ) (c : ℕ → Ideal R) :
    Ideal.map f (∏ j ∈ s, c j) = ∏ j ∈ s, Ideal.map f (c j) := by
  classical
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.map_top,
      Ideal.one_eq_top]
  | cons a s ha ih => rw [Finset.prod_cons, Ideal.map_mul, ih, Finset.prod_cons]

namespace AlgebraicGeometry

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### Restricting the local equations of the divisors -/

/-- **The local equations of the divisors restrict to a smaller affine open.** If `D_j` is cut out
by `e_{j+1}` on an affine open `V` for `j + 1 ≤ N` and is empty from `N` on, the same holds on
every affine open contained in `V`, with the restricted equations: the ideal of a quasi-coherent
ideal sheaf datum restricts by `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`.

Only these two clauses of the chart data of [Stacks, Tag 0ESU] restrict so cheaply — no flatness
is involved — and they are all that the local finiteness of the two filtrations needs. -/
theorem exists_forall_ideal_eq_span_and_eq_top_of_le {D : ℕ → X.IdealSheafData}
    {V : X.affineOpens} {m : ℕ} {e : ℕ → Γ(X, V.1)}
    (hlow : ∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)})
    (htop : ∀ j, m ≤ j → (D j).ideal V = ⊤)
    {U : X.affineOpens} (h : U.1 ≤ V.1) :
    ∃ e' : ℕ → Γ(X, U.1),
      (∀ j, j + 1 ≤ m → (D j).ideal U = Ideal.span {e' (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal U = ⊤) := by
  refine ⟨fun k => (X.presheaf.map (homOfLE h).op).hom (e k), fun j hj => ?_, fun j hj => ?_⟩
  · rw [← Scheme.IdealSheafData.map_ideal (D j) h, hlow j hj, Ideal.map_span,
      Set.image_singleton]
    rfl
  · rw [← Scheme.IdealSheafData.map_ideal (D j) h, htop j hj, Ideal.map_top]

/-- **The chart data of [Stacks, Tag 0ESU] is available on a basis of the topology.** Around every
point of an open `B` there is an affine open contained in `B` carrying local equations for the
divisors, nonzerodivisors and units past the last index, with the product formula for the Fitting
ideals.

The chart hypothesis gives an affine open `V` around the point; a basic open `D(g)` of `V` inside
`B` inherits everything, the ideals by
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_basicOpen` and the nonzerodivisors by
`IsLocalization.map_nonZeroDivisors_le`, since `Γ(X, D(g))` is a localization of `Γ(X, V)`. -/
theorem exists_affineOpen_le_chart {D : ℕ → X.IdealSheafData} (F : X.Modules)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal V = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, m < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) m, Ideal.span {e j} ^ (j - k)))
    (B : X.Opens) {x : X} (hxB : x ∈ B) :
    ∃ W : X.affineOpens, W.1 ≤ B ∧ x ∈ (W.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, W.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal W = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal W = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, W.1)) ∧
      (∀ j, m < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal W =
        ∏ j ∈ Finset.Icc (k + 1) m, Ideal.span {e j} ^ (j - k)) := by
  classical
  obtain ⟨V, hxV, m, e, hlow, htop, hmem, hunit, hprod⟩ := hchart x
  obtain ⟨g, hgB, hxg⟩ := V.2.exists_basicOpen_le (⟨x, hxB⟩ : B) hxV
  set φ := (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom with hφ
  have hres : IsLocalization.Away g Γ(X, X.basicOpen g) := V.2.isLocalization_basicOpen g
  refine ⟨X.affineBasicOpen g, hgB, hxg, m, fun j => φ (e j), fun j hj => ?_, fun j hj => ?_,
    fun j => ?_, fun j hj => (hunit j hj).map _, fun k => ?_⟩
  · rw [← (D j).map_ideal_basicOpen V g, hlow j hj, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← (D j).map_ideal_basicOpen V g, htop j hj, Ideal.map_top]
    rfl
  · refine IsLocalization.map_nonZeroDivisors_le (M := Submonoid.powers g)
      (S := Γ(X, X.basicOpen g)) ?_
    rw [hφ, ← RingHom.algebraMap_toAlgebra (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom]
    exact ⟨e j, hmem j, rfl⟩
  · rw [← (fittingIdeal F (k : ℤ)).map_ideal_basicOpen V g, hprod k,
      Ideal.map_finsetProd φ]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton]
    rfl

/-! ### The two endpoints -/

/-- **Stacks Project, Tag 0ESU: the increasing filtration starts at the zero subsheaf**,
`F⁰ = 0`.

The ring-level statement is `Stacks.FittingFiltration.incr_zero_eq_bot`: the product
`e_1 ⋯ e_N` of all the local equations annihilates the sections. It applies on the affine opens of
`AlgebraicGeometry.exists_affineOpen_le_chart`, which form a basis of the topology, and vanishing
of a section is a local condition. -/
theorem fittingIncr_zero_eq_bot {D : ℕ → X.IdealSheafData} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal V = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, m < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) m, Ideal.span {e j} ^ (j - k))) :
    fittingIncr D F 0 = ⊥ := by
  refine le_antisymm (SheafOfModules.Submodule.le_iff.mpr
    (PresheafOfModules.Submodule.le_iff.mpr fun U s hs => ?_)) bot_le
  obtain ⟨U, rfl⟩ : ∃ U₀ : X.Opens, op U₀ = U := ⟨U.unop, rfl⟩
  refine mem_submodule_of_locally_mem (⊥ : F.Submodule) U s fun x hx => ?_
  obtain ⟨W, hWU, hxW, m, e, hlow, htop, hmem, hunit, hprod⟩ :=
    exists_affineOpen_le_chart F hchart U hx
  have : Module.Finite Γ(X, W.1) Γ(F, W.1) := moduleFinite_sections_on_affine F W.1 W.2
  have hbot : sectionsSubmodule (fittingIncr D F 0) W.1 = ⊥ := by
    rw [sectionsSubmodule_fittingIncr hD W hlow htop 0]
    exact incr_zero_eq_bot hmem hunit fun k =>
      (fittingIdeal_ideal F (k : ℤ) W).symm.trans (hprod k)
  refine ⟨W.1, hWU, hxW, ?_⟩
  rw [SheafOfModules.Submodule.bot_obj]
  have hmemW : (ConcreteCategory.hom (F.val.map (homOfLE hWU).op)) s ∈
      sectionsSubmodule (fittingIncr D F 0) W.1 :=
    val_map_mem_submodule (fittingIncr D F 0) (homOfLE hWU).op hs
  exact hbot.le hmemW

/-- **Stacks Project, Tag 0ESU: the decreasing filtration starts at the whole module in degree
one**, `F₁ = ℱ`.

The ring-level statement is `Stacks.FittingFiltration.decr_one_eq_top`. As for
`AlgebraicGeometry.fittingIncr_zero_eq_bot` it is available on the basic opens of the charts,
which form a basis of the topology, and membership in a subsheaf is local; a subsheaf containing
every section over every affine open is everything, by
`AlgebraicGeometry.sheafSubmodule_eq_top_of_affine`. -/
theorem fittingDecr_one_eq_top {D : ℕ → X.IdealSheafData} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal V = ⊤) ∧
      (∀ j, e j ∈ nonZeroDivisors Γ(X, V.1)) ∧
      (∀ j, m < j → IsUnit (e j)) ∧
      (∀ k : ℕ, (fittingIdeal F (k : ℤ)).ideal V =
        ∏ j ∈ Finset.Icc (k + 1) m, Ideal.span {e j} ^ (j - k))) :
    fittingDecr D F 1 = ⊤ := by
  refine sheafSubmodule_eq_top_of_affine _ fun U => ?_
  intro s _
  refine mem_submodule_of_locally_mem (fittingDecr D F 1) U.1 s fun x hx => ?_
  obtain ⟨W, hWU, hxW, m, e, hlow, htop, hmem, hunit, hprod⟩ :=
    exists_affineOpen_le_chart F hchart U.1 hx
  have : Module.Finite Γ(X, W.1) Γ(F, W.1) := moduleFinite_sections_on_affine F W.1 W.2
  have htopW : sectionsSubmodule (fittingDecr D F 1) W.1 = ⊤ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, sectionsSubmodule_fittingDecr hD W hlow htop 0]
    exact decr_one_eq_top hmem hunit fun k =>
      (fittingIdeal_ideal F (k : ℤ) W).symm.trans (hprod k)
  exact ⟨W.1, hWU, hxW, htopW.ge Submodule.mem_top⟩

/-! ### Local finiteness -/

/-- **A subsheaf with no sections over the opens of `V` restricts to zero on `V`.** Every germ at
a point of `V` is the germ of a section over an open contained in `V`, and there are none but
zero. -/
theorem isZero_pullback_asModules_of_forall_obj_eq_bot {F : X.Modules} (N : F.Submodule)
    (O : X.Opens) (hN : ∀ W : X.Opens, W ≤ O → N.toSubmodule.obj (op W) = ⊥) :
    IsZero ((Scheme.Modules.pullback O.ι).obj N.asModules) := by
  refine Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_pullback_of_forall_isZero_stalk
    O.ι N.asModules fun z => ?_
  have hz : (O.ι z : X) ∈ O := z.2
  have key : ∀ t : ToType ((N.asModules : X.Modules).presheaf.stalk (O.ι z)), t = 0 := by
    intro t
    obtain ⟨U, hxU, s, hs⟩ :=
      TopCat.Presheaf.exists_germ_eq (N.asModules : X.Modules).presheaf t
    have hzW : (O.ι z : X) ∈ U ⊓ O := ⟨hxU, hz⟩
    have hsub : Subsingleton Γ((N.asModules : X.Modules), U ⊓ O) := by
      have h0 (a : Γ((N.asModules : X.Modules), U ⊓ O)) : a.1 = 0 :=
        (_root_.Submodule.mem_bot _).1 ((hN (U ⊓ O) inf_le_right).le a.2)
      exact ⟨fun a b => Subtype.ext ((h0 a).trans (h0 b).symm)⟩
    have hres : (ConcreteCategory.hom ((N.asModules : X.Modules).presheaf.map
        (homOfLE (inf_le_left : U ⊓ O ≤ U)).op)) s = 0 := hsub.elim _ _
    have hgerm := TopCat.Presheaf.germ_res_apply ((N.asModules : X.Modules).presheaf)
      (homOfLE (inf_le_left : U ⊓ O ≤ U)) (O.ι z) hzW s
    rw [hres, map_zero] at hgerm
    exact hs.symm.trans hgerm.symm
  have : Subsingleton (ToType ((N.asModules : X.Modules).presheaf.stalk (O.ι z))) :=
    ⟨fun a b => (key a).trans (key b).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **Stacks Project, Tag 0ESU: the increasing filtration is locally exhaustive.** Around every
point there is an open `V` and an index `N` beyond which the cokernel of `Fⁿ ⟶ ℱ` vanishes on
`V`: the filtration exhausts `ℱ` near every point, with a bound that depends on the point.

On a chart with equations `e_1, …, e_N` the tail product `e_{n+1} ⋯ e_N` is empty for `n ≥ N`, so
`Fⁿ` is all of `ℱ` there — by `Stacks.FittingFiltration.incr_eq_top` — and the same holds on every
affine open inside the chart, by
`AlgebraicGeometry.exists_forall_ideal_eq_span_and_eq_top_of_le`. A quotient by a subsheaf that is
everything on the affine opens of `V` has vanishing stalks on `V`, by
`Stacks.SheafOfModules.subsingleton_stalk_cokernel_submodule_ι`. -/
theorem exists_isZero_pullback_cokernel_fittingIncr {D : ℕ → X.IdealSheafData} (F : X.Modules)
    [F.IsQuasicoherent] (hD : IsLocallyFiniteFamily D)
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal V = ⊤))
    (x : X) :
    ∃ V : X.Opens, x ∈ (V : Set X) ∧ ∃ m : ℕ, ∀ n ≥ m,
      IsZero ((Scheme.Modules.pullback V.ι).obj
        (cokernel (C := X.Modules) (fittingIncr D F n).ι)) := by
  obtain ⟨V, hxV, m, e, hlow, htop⟩ := hchart x
  refine ⟨V.1, hxV, m, fun n hn => ?_⟩
  have hall : ∀ U : X.affineOpens, U.1 ≤ V.1 →
      (fittingIncr D F n).toSubmodule.obj (op U.1) = ⊤ := by
    intro U hU
    obtain ⟨e', hlow', htop'⟩ := exists_forall_ideal_eq_span_and_eq_top_of_le hlow htop hU
    change sectionsSubmodule (fittingIncr D F n) U.1 = ⊤
    rw [sectionsSubmodule_fittingIncr hD U hlow' htop' n]
    exact incr_eq_top _ hn
  refine Stacks.AlgebraicGeometry.FlatPullbackStalk.isZero_pullback_of_forall_isZero_stalk
    V.1.ι _ fun z => ?_
  have := Stacks.SheafOfModules.subsingleton_stalk_cokernel_submodule_ι
    (fittingIncr D F n) hall (x := (V.1.ι z : X)) z.2
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- **Stacks Project, Tag 0ESU: the decreasing filtration is locally separated.** Around every
point there is an open `V` and an index `N` beyond which `F_n` itself vanishes on `V`: the
filtration reaches zero near every point, with a bound that depends on the point.

On a chart with equations `e_1, …, e_N` the product `e_n ⋯ e_N` is empty for `n > N`, so `F_n` is
zero there — by `Stacks.FittingFiltration.decr_eq_bot` — and the vanishing spreads from the chart
to all of its opens by `AlgebraicGeometry.submodule_obj_eq_bot_of_le_affine`, the decreasing
filtration being quasi-coherent. -/
theorem exists_isZero_pullback_fittingDecr {D : ℕ → X.IdealSheafData} (F : X.Modules)
    [F.IsQuasicoherent] (hD : IsLocallyFiniteFamily D)
    (hcart : ∀ j, IsEffectiveCartierDivisor (D j))
    (hchart : ∀ x : X, ∃ V : X.affineOpens, x ∈ (V.1 : Set X) ∧ ∃ (m : ℕ) (e : ℕ → Γ(X, V.1)),
      (∀ j, j + 1 ≤ m → (D j).ideal V = Ideal.span {e (j + 1)}) ∧
      (∀ j, m ≤ j → (D j).ideal V = ⊤))
    (x : X) :
    ∃ V : X.Opens, x ∈ (V : Set X) ∧ ∃ m : ℕ, ∀ n ≥ m,
      IsZero ((Scheme.Modules.pullback V.ι).obj (fittingDecr D F n).asModules) := by
  obtain ⟨V, hxV, m, e, hlow, htop⟩ := hchart x
  refine ⟨V.1, hxV, m + 1, fun n hn => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, n = i + 1 := ⟨n - 1, by omega⟩
  have hqcN := isQuasicoherent_fittingDecr_of_isEffectiveCartierDivisor D F hD hcart (i + 1)
  have hVbot : (fittingDecr D F (i + 1)).toSubmodule.obj (op V.1) = ⊥ := by
    change sectionsSubmodule (fittingDecr D F (i + 1)) V.1 = ⊥
    rw [sectionsSubmodule_fittingDecr hD V hlow htop i]
    exact decr_eq_bot _ (show m < i + 1 by omega)
  exact isZero_pullback_asModules_of_forall_obj_eq_bot (fittingDecr D F (i + 1)) V.1
    fun W hW => submodule_obj_eq_bot_of_le_affine _ hqcN V.2 hVbot hW

/-! ### Canonicity -/

/-- **A subsheaf along which every endomorphism of the ambient module lifts is carried onto itself
by every automorphism.** The hypothesis is that for every endomorphism `φ` of `ℱ` there is a
morphism of the subsheaf to itself compatible with the inclusions; applying it to `e.hom` gives
one inclusion and to `e.inv` the other.

The image of the subsheaf along the automorphism is
`AlgebraicGeometry.Scheme.Modules.rangeSubmodule`, the sectionwise range of the composite of the
inclusion with the automorphism. -/
theorem rangeSubmodule_ιModules_comp {F : X.Modules} (N : F.Submodule) (e : F ≅ F)
    (lift : ∀ φ : F ⟶ F, ∃ ψ : N.asModules ⟶ N.asModules,
      ψ ≫ N.ιModules = N.ιModules ≫ φ) :
    Scheme.Modules.rangeSubmodule (N.ιModules ≫ e.hom) = N := by
  obtain ⟨ψ, hψ⟩ := lift e.hom
  obtain ⟨χ, hχ⟩ := lift e.inv
  have hιN : Scheme.Modules.rangeSubmodule N.ιModules = N :=
    Scheme.Modules.rangeSubmodule_ι N
  refine le_antisymm
    ((Scheme.Modules.rangeSubmodule_le_rangeSubmodule_of_comm ψ hψ).trans hιN.le)
    (hιN.ge.trans (Scheme.Modules.rangeSubmodule_le_rangeSubmodule_of_comm χ ?_))
  rw [← Category.assoc, hχ, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- **Stacks Project, Tag 0ESU: the increasing filtration is canonical.** Every automorphism of
`ℱ` carries each term `Fⁱ` onto itself.

`Fⁱ = ℐ_{i+1} · ℱ` is functorial in `ℱ` by `AlgebraicGeometry.idealPowSmulMap`, so every
endomorphism of `ℱ` lifts to it compatibly with the inclusion. No chart and no hypothesis on the
divisors is involved: this is what it means for the filtration to be defined by the ideal sheaves
rather than by local equations. -/
theorem rangeSubmodule_fittingIncr_comp {D : ℕ → X.IdealSheafData} (F : X.Modules)
    [F.IsQuasicoherent] (e : F ≅ F) (i : ℕ) :
    Scheme.Modules.rangeSubmodule ((fittingIncr D F i).ιModules ≫ e.hom) = fittingIncr D F i :=
  rangeSubmodule_ιModules_comp (fittingIncr D F i) e fun φ =>
    ⟨idealPowSmulMap (divisorTail D (i + 1)) 1 φ,
      idealPowSmulMap_comp_ι (divisorTail D (i + 1)) 1 φ⟩

/-- **Stacks Project, Tag 0ESU: the decreasing filtration is canonical.** Every automorphism of
`ℱ` carries each term `F_i` onto itself.

`F_i = Ann_ℱ(ℐ_i)` receives every morphism out of a module that `ℐ_i` annihilates, by
`Stacks.SheafOfModules.annihilatorLift`, and `ℐ_i` annihilates `F_i` itself; so every
endomorphism of `ℱ` lifts to `F_i` compatibly with the inclusion. As for the increasing
filtration no chart and no hypothesis on the divisors is involved. -/
theorem rangeSubmodule_fittingDecr_comp {D : ℕ → X.IdealSheafData} (F : X.Modules) (e : F ≅ F)
    (i : ℕ) :
    Scheme.Modules.rangeSubmodule ((fittingDecr D F i).ιModules ≫ e.hom) = fittingDecr D F i :=
  rangeSubmodule_ιModules_comp (fittingDecr D F i) e fun φ =>
    ⟨Stacks.SheafOfModules.annihilatorLift F (mul_comm_ringCatSheaf X)
        (idealSubsheaf (divisorTail D i))
        (fun W a ha mm => Stacks.SheafOfModules.smul_annihilatorSubmodule_eq_zero F
          (mul_comm_ringCatSheaf X) (idealSubsheaf (divisorTail D i)) W a ha mm)
        ((fittingDecr D F i).ι ≫ φ),
      Stacks.SheafOfModules.annihilatorLift_comp_ι F (mul_comm_ringCatSheaf X)
        (idealSubsheaf (divisorTail D i)) _ _⟩

end AlgebraicGeometry

end
