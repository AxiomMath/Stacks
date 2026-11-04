module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Maps.Proper.UniversallyClosed
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.Topology.Maps.Proper
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Characterizations of proper maps of topological spaces

For a continuous map `f : X → Y` of topological spaces the following conditions all agree with
properness of `f`: being closed with quasi-compact fibres; being closed and quasi-proper;
being closed after every base change `Z × X → Z × Y`; and having a closed first projection out
of every topological fibre product `Z ×_Y X → Z`. No separation hypothesis is imposed on any
of the spaces involved.

## Main definitions

* `IsQuasiCompactSubset`: a subset of a topological space is quasi-compact.
* `IsQuasiProper`: the preimage of every quasi-compact subset is quasi-compact.
* Bourbaki-properness is `StacksDraft.Topology.IsBourbakiProperMap` (Stacks 005O (2)), which
  this file uses at a single universe.
* `FibreProduct`: the topological fibre product `Z ×_Y X` of `g : Z → Y` and `f : X → Y`,
  carrying the subspace topology of `Z × X`.
* `fibreProductFst`: the first projection `Z ×_Y X → Z`.
* `IsUniversallyClosed`: the first projection `Z ×_Y X → Z` is closed for every continuous
  `g : Z → Y`.

## Main results

* `isProperMap_tfae`: the four conditions above are equivalent for a continuous map.
-/

@[expose] public section

universe u

open StacksDraft.Topology (IsBourbakiProperMap)

/-! ### Quasi-properness, Bourbaki-properness and universal closedness -/

/-- A subset is *quasi-compact* iff it is compact; no separation hypothesis is assumed on the
ambient space. -/
@[ega "0 2.1.3"]
def IsQuasiCompactSubset {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  IsCompact A

/-- `f` is *quasi-proper* if the preimage of every quasi-compact subset is quasi-compact. -/
def IsQuasiProper {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ V : Set Y, IsQuasiCompactSubset V → IsQuasiCompactSubset (f ⁻¹' V)

/-- The topological fibre product `Z ×_Y X` of `g : Z → Y` and `f : X → Y`, realized as the
subtype of pairs `(z, x)` with `g z = f x`. -/
@[implicit_reducible, ega "I 3.4.2"]
def FibreProduct {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Z → Y) : Type _ :=
  {p : Z × X // g p.1 = f p.2}

/-- The subspace topology on the topological fibre product `Z ×_Y X`, inherited from `Z × X`. -/
instance instTopologicalSpaceFibreProduct {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : X → Y) (g : Z → Y) : TopologicalSpace (FibreProduct f g) :=
  instTopologicalSpaceSubtype

/-- First projection `Z ×_Y X → Z`. -/
def fibreProductFst {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Z → Y) :
    FibreProduct f g → Z :=
  fun p => p.val.1

/-- The first projection sends a point of `Z ×_Y X` to its `Z`-coordinate. -/
lemma fibreProductFst_apply {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) (g : Z → Y) (p : FibreProduct f g) :
    fibreProductFst f g p = p.val.1 :=
  rfl

/-- `f` is *universally closed* if, for every continuous `g : Z → Y`, the first
projection from the topological fibre product `Z ×_Y X → Z` is closed. -/
def IsUniversallyClosed {X : Type u} {Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) : Prop :=
  ∀ (Z : Type u) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (fibreProductFst f g)

/-! ### Swapping the factors of a product -/

/-- Swapping the two factors of a product of topological spaces, as a homeomorphism. -/
private noncomputable def swapHomeo (A B : Type*) [TopologicalSpace A] [TopologicalSpace B] :
    (A × B) ≃ₜ (B × A) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_swap
  continuous_invFun := continuous_swap

/-- `Prod.map id f` is conjugate to `Prod.map f id` via swapping factors. -/
private lemma prodMap_id_f_eq_swap {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : X → Y) :
    (Prod.map (id : Z → Z) f) =
      Prod.swap ∘ (Prod.map f (id : Z → Z)) ∘ Prod.swap := by
  funext ⟨z, x⟩; rfl

/-! ### Universal closedness versus Bourbaki-properness -/

/-- A universally closed continuous map is Bourbaki-proper: apply universal closedness to
`g := (Prod.snd : Z × Y → Y)`, for which `(Z × Y) ×_Y X ≃ₜ Z × X` and `fibreProductFst`
becomes `Prod.map id f`. -/
private lemma isBourbakiProper_of_isUniversallyClosed {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hf : Continuous f) (huc : IsUniversallyClosed f) :
    IsBourbakiProperMap.{u, u, u} f := by
  intro Z _
  let e : (Z × X) ≃ₜ FibreProduct f (Prod.snd : Z × Y → Y) :=
    { toFun := fun p => ⟨((p.1, f p.2), p.2), rfl⟩
      invFun := fun p => (p.val.1.1, p.val.2)
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨⟨z, y⟩, x⟩, hyfx⟩
        obtain rfl : y = f x := hyfx
        rfl
      continuous_toFun := Continuous.subtype_mk
        ((continuous_fst.prodMk (hf.comp continuous_snd)).prodMk continuous_snd) _
      continuous_invFun :=
        (continuous_fst.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_snd.comp continuous_subtype_val) }
  exact (huc (Z × Y) Prod.snd continuous_snd).comp e.isClosedMap

/-- A Bourbaki-proper map is universally closed: given continuous `g : Z → Y`, factor
`fibreProductFst f g` through the graph map `z ↦ (z, g z)`. -/
private lemma isUniversallyClosed_of_isBourbakiProper {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X → Y) (hb : IsBourbakiProperMap.{u, u, u} f) :
    IsUniversallyClosed f := by
  intro Z _ g hg C hC
  obtain ⟨D', hD', rfl⟩ := isClosed_induced_iff.mp hC
  convert (hb Z _ hD').preimage (continuous_id.prodMk hg) using 1
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.val, hp, Prod.ext rfl p.property.symm⟩
  · rintro ⟨zx, hzx, hmap⟩
    obtain ⟨h₁, h₂⟩ : zx.1 = z ∧ f zx.2 = g z :=
      ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩
    exact ⟨⟨zx, by rw [h₁, h₂]⟩, hzx, h₁⟩

/-! ### The main equivalence -/

/-- **Stacks 005R**.
Let `f : X → Y` be a continuous map between topological spaces. The following four
conditions are equivalent:

1. `f` is quasi-proper and closed.
2. `f` is Bourbaki-proper.
3. `f` is universally closed.
4. `f` is closed and the fibre `f⁻¹{y}` is quasi-compact for every `y : Y`. -/
@[stacks 005R]
theorem isProperMap_tfae {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) :
    [IsQuasiProper f ∧ IsClosedMap f,
     IsBourbakiProperMap.{u, u, u} f,
     IsUniversallyClosed f,
     IsClosedMap f ∧ ∀ y : Y, IsQuasiCompactSubset (f ⁻¹' {y})].TFAE := by
  -- Step (1) ↔ proper map.
  have h1_iff_proper : (IsQuasiProper f ∧ IsClosedMap f) ↔ IsProperMap f :=
    ⟨fun ⟨hqp, hcl⟩ => isProperMap_iff_isClosedMap_and_compact_fibers.mpr
        ⟨hf, hcl, fun y => hqp {y} isCompact_singleton⟩,
      fun hp => ⟨fun _ hV => hp.isCompact_preimage hV, hp.isClosedMap⟩⟩
  -- Step (4) ↔ proper map.
  have h4_iff_proper :
      (IsClosedMap f ∧ ∀ y, IsQuasiCompactSubset (f ⁻¹' {y})) ↔ IsProperMap f := by
    rw [isProperMap_iff_isClosedMap_and_compact_fibers]
    exact ⟨fun ⟨hcl, hfib⟩ => ⟨hf, hcl, hfib⟩, fun ⟨_, hcl, hfib⟩ => ⟨hcl, hfib⟩⟩
  -- Step (2) ↔ proper map (Mathlib uses `Prod.map f id`; we use `Prod.map id f`,
  -- conjugate by `Prod.swap`).
  have h2_iff_proper : IsBourbakiProperMap.{u, u, u} f ↔ IsProperMap f := by
    rw [isProperMap_iff_universally_closed]
    refine ⟨fun hb => ⟨hf, fun Z _ => ?_⟩, fun ⟨_, hu⟩ Z _ => ?_⟩
    · exact (swapHomeo Z Y).isClosedMap.comp <| (hb Z).comp (swapHomeo X Z).isClosedMap
    · exact (swapHomeo Y Z).isClosedMap.comp <| (hu Z).comp (swapHomeo Z X).isClosedMap
  -- Step (3) ↔ (2), bridging `FibreProduct` against Mathlib's `Prod.map f id` formulation.
  have h3_iff_2 : IsUniversallyClosed f ↔ IsBourbakiProperMap.{u, u, u} f :=
    ⟨isBourbakiProper_of_isUniversallyClosed f hf, isUniversallyClosed_of_isBourbakiProper f⟩
  tfae_have 1 ↔ 2 := h1_iff_proper.trans h2_iff_proper.symm
  tfae_have 2 ↔ 3 := h3_iff_2.symm
  tfae_have 1 ↔ 4 := h1_iff_proper.trans h4_iff_proper.symm
  tfae_finish
