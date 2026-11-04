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
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lifting specializations along closed and open maps

Specializations lift along a closed continuous map. Generalizations lift along an open
continuous map from a Noetherian space in which every irreducible closed subset has a generic
point, provided the target is `T₀`.

## Main definitions

* `SpecializationPair`, `Generalization`: the specialization relation on a space.
* `SpecializationsLiftAlong`, `GeneralizationsLiftAlong`: the lifting properties of a map.
* `ClosedMap`, `OpenMap`: closed and open maps.

## Main results

* `specializations_lift_of_isClosedMap`: specializations lift along a closed map.
* `generalizations_lift_of_isOpenMap`: generalizations lift along such an open map.
-/

@[expose] public section

open TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `x'` is a specialization of `x`, written `x ⤳ x'`. -/
@[ega "0 2.1.2", sga "1 IV 6.3", sga "4 IV 4.2.2", sga "7 IX 3.1"]
def SpecializationPair (x x' : X) : Prop := x ⤳ x'

/-- `x` is a generalization of `x'`, i.e. `x' ∈ closure {x}`. -/
@[ega "0 2.1.2",
  ega "I 2.4.2",
  ega "IV 15.5.6.1" "partial",
  ega "IV 21.13.15",
  sga "1 IV 6.3",
  sga "4 IV 4.2.2"]
def Generalization (x x' : X) : Prop := x ⤳ x'

/-- Specializations lift along `f`: every specialization of `f x` is the image of a
specialization of `x`. -/
@[ega "II 7.2.1"]
def SpecializationsLiftAlong (f : X → Y) : Prop :=
  ∀ (x : X) (y' : Y), (f x) ⤳ y' → ∃ x' : X, x ⤳ x' ∧ f x' = y'

/-- Generalizations lift along `f`: every generalization of `f x` is the image of a
generalization of `x`. -/
@[ega "IV 2.3.4"]
def GeneralizationsLiftAlong (f : X → Y) : Prop :=
  ∀ (x : X) (y' : Y), y' ⤳ f x → ∃ x' : X, x' ⤳ x ∧ f x' = y'

/-- A map that takes closed sets to closed sets. -/
@[ega "I 2.2.6"]
def ClosedMap (f : X → Y) : Prop := IsClosedMap f

/-- A map that takes open sets to open sets. -/
@[ega "I 2.2.6", sga "1 IV 6.6"]
def OpenMap (f : X → Y) : Prop := IsOpenMap f

/-- **Stacks 0066** (1).
If `f` is a closed continuous map, then specializations lift along `f`. -/
@[stacks 0066 "(1)", ega "II 7.2.1" "a ⇒ b"]
theorem specializations_lift_of_isClosedMap
    (f : X → Y) (hf_cont : Continuous f) (hf_closed : IsClosedMap f) :
    SpecializationsLiftAlong f := by
  have := hf_cont
  exact fun _ _ h ↦ hf_closed.specializingMap h

/-- **Stacks 0066** (2).
If `f : X → Y` is an open continuous map, `X` is Noetherian with a generic point for every
irreducible closed subset, and `Y` is `T₀`, then generalizations lift along `f`. -/
@[stacks 0066 "(2)",
  ega "IV 1.10.3" "a) ⇒ b)",
  ega "IV 1.10.4" "a) ⇒ b), special case",
  ega "IV 14.1.6" "special case",
  ega "IV 2.3.5" "(i), special case", sga "1 IV 6.5" "partial"]
theorem generalizations_lift_of_isOpenMap
    (f : X → Y) (hf_cont : Continuous f) (hf_open : IsOpenMap f)
    [hX_noeth : NoetherianSpace X]
    (hX_generic : ∀ (Z : Set X), IsIrreducible Z → IsClosed Z →
                    ∃ η : X, IsGenericPoint η Z)
    [hY_t0 : T0Space Y] :
    GeneralizationsLiftAlong f := by
  intro x y' h
  -- Fiber `A := f ⁻¹' {y'}` and its closure `C`; show `x ∈ C` using openness of `f`.
  set A : Set X := f ⁻¹' {y'}
  have hxC : x ∈ closure A := mem_closure_iff.mpr fun U hU hxU ↦
    specializes_iff_forall_open.mp h (f '' U) (hf_open U hU) ⟨x, hxU, rfl⟩
  set C : Set X := closure A
  -- Pick an irreducible component `Z` of `C` through `x` and an open subset of `Z`.
  have : NoetherianSpace C := NoetherianSpace.set C
  let xC : C := ⟨x, hxC⟩
  set Z : Set C := irreducibleComponent xC
  have hZ_mem : Z ∈ irreducibleComponents C :=
    irreducibleComponent_mem_irreducibleComponents xC
  obtain ⟨o, ho_open, ho_ne, ho_sub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ_mem
  -- Density of `A` in `C` gives some `v ∈ A` whose image in `C` lies in `Z`.
  obtain ⟨U, hU_open, hU_eq⟩ := isOpen_induced_iff.mp ho_open
  obtain ⟨c₀, hc₀⟩ := ho_ne
  rw [← hU_eq] at hc₀
  obtain ⟨v, hvU, hv_A⟩ := mem_closure_iff.mp c₀.2 U hU_open hc₀
  -- Transport `Z` to a closed irreducible `Z_X ⊆ X` and take its generic point `η`.
  obtain ⟨η, hη_gen⟩ := hX_generic (((↑) : C → X) '' Z)
    (hZ_mem.1.image _ continuous_subtype_val.continuousOn)
    ((isClosed_closure.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed).mp
      (isClosed_of_mem_irreducibleComponents Z hZ_mem))
  -- `η ⤳ x` and `f η ⤳ y'`.
  have hη_spec_x : η ⤳ x := hη_gen.specializes ⟨xC, mem_irreducibleComponent, rfl⟩
  have hfη_spec_y : f η ⤳ y' :=
    hv_A ▸ (hη_gen.specializes
      ⟨(⟨v, subset_closure hv_A⟩ : C), ho_sub (hU_eq ▸ hvU), rfl⟩).map hf_cont
  -- `y' ⤳ f η`, because `η ∈ C = closure A` and `f` is continuous.
  have hy_spec_fη : y' ⤳ f η := by
    obtain ⟨c, _, hcη⟩ := hη_gen.mem
    exact specializes_iff_mem_closure.mpr <|
      closure_mono (Set.image_preimage_subset f {y'}) <|
        image_closure_subset_closure_image hf_cont ⟨η, hcη ▸ c.2, rfl⟩
  -- By T₀ antisymmetry of specialization, `f η = y'`.
  exact ⟨η, hη_spec_x, (hfη_spec_y.antisymm hy_spec_fη).eq⟩

