module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.Topology.Dimension.NowhereDense
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Strict dimension drops for closed subsets, specializations and fibres

This file proves three strict upper bounds on topological Krull dimension:

* a closed subscheme of an irreducible Noetherian scheme which is not all of it has strictly
  smaller dimension;
* a subset of a space all of whose points specialize to a closed point outside the subset has
  strictly smaller dimension than the space;
* the fibres of a dominant morphism `f : X ⟶ P`, locally of finite type, from an irreducible
  quasi-compact Noetherian scheme to a Jacobson scheme with at least two points, have dimension
  strictly smaller than `X`.

## Main results

* `Stacks.EtaleCohomology.topologicalKrullDim_add_one_le_of_isClosedImmersion`: a non-surjective
  closed immersion into an irreducible Noetherian scheme drops the dimension.
* `Stacks.EtaleCohomology.topologicalKrullDim_add_one_le_of_forall_specializes`: a subset whose
  points all specialize to closed points outside it has strictly smaller dimension.
* `Stacks.EtaleCohomology.topologicalKrullDim_fiber_add_one_le_of_isDominant`: the fibres of a
  dominant morphism, locally of finite type, to a Jacobson scheme with at least two points have
  strictly smaller dimension.

## References

* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Topology

universe u

namespace Stacks.EtaleCohomology

/-- In `WithBot ℕ∞`, a value bounded by every natural number is `⊤`. -/
theorem eq_top_of_forall_natCast_le {b : WithBot ℕ∞} (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ b) :
    b = ⊤ := by
  induction b using WithBot.recBotCoe with
  | bot => exact absurd (h 0) (by simp)
  | coe e =>
    have he : ∀ n : ℕ, (n : ℕ∞) ≤ e := fun n ↦ by exact_mod_cast h n
    by_contra hne
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, e = m := ENat.ne_top_iff_exists.1 (fun h' ↦ hne (by rw [h']; rfl))
      |>.imp fun _ h ↦ h.symm
    have := he (m + 1)
    norm_cast at this
    omega

/-- To bound `a + 1 ≤ b` in `WithBot ℕ∞` it suffices to bound `n + 1 ≤ b` for every natural
number `n ≤ a`. -/
theorem add_one_le_of_forall_natCast_le {a b : WithBot ℕ∞}
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ a → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ b) : a + 1 ≤ b := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have hb : b = ⊤ := eq_top_of_forall_natCast_le fun n ↦
        (WithBot.coe_le_coe.2 (by exact_mod_cast Nat.le_succ n)).trans
          (h n (by exact WithBot.coe_le_coe.2 le_top))
      rw [hb]
      exact le_top
    | coe n => exact_mod_cast h n le_rfl

/-- In `WithBot ℕ∞`, `a + 1 ≤ n + 1` gives `a ≤ n`. -/
theorem le_natCast_of_add_one_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + 1 ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) : a ≤ n := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : (((⊤ : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (((n + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast h
      rw [top_add] at h'
      exact absurd (WithBot.coe_le_coe.1 h') (by simp)
    | coe m =>
      have : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h
      have : m + 1 ≤ n + 1 := by exact_mod_cast this
      exact_mod_cast (by omega : m ≤ n)

/-- **A subset whose points all specialize to closed points outside it has strictly smaller
dimension.** If every point of `S ⊆ X` specializes to a closed point of `X` not in `S`, then
`dim S + 1 ≤ dim X`. -/
theorem topologicalKrullDim_add_one_le_of_forall_specializes {X : Type*} [TopologicalSpace X]
    (S : Set X) (h : ∀ x ∈ S, ∃ y : X, x ⤳ y ∧ IsClosed ({y} : Set X) ∧ y ∉ S) :
    topologicalKrullDim S + 1 ≤ topologicalKrullDim X := by
  refine add_one_le_of_forall_natCast_le fun n hn ↦ ?_
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.1 hn
  let φ := IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val
  have hφ : StrictMono φ := IrreducibleCloseds.map_strictMono_of_isInducing .subtypeVal
  obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
  obtain ⟨y, hxy, hyc, hyS⟩ := h x.1 x.2
  let c : IrreducibleCloseds X := ⟨{y}, isIrreducible_singleton, hyc⟩
  have hc : c < φ p.head := by
    refine lt_of_le_of_ne (fun z hz ↦ ?_) fun heq ↦ ?_
    · rw [Set.mem_singleton_iff.1 hz]
      exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_image_of_mem _ hx))
        (specializes_iff_mem_closure.1 hxy)
    · have hxc : x.1 ∈ (c : Set X) := by
        rw [heq]
        exact subset_closure (Set.mem_image_of_mem _ hx)
      exact hyS ((Set.mem_singleton_iff.1 hxc) ▸ x.2)
  exact Order.le_krullDim_iff.2
    ⟨(p.map φ hφ).cons c hc, by simp [RelSeries.cons, RelSeries.append, hp]⟩

/-- In an irreducible space a closed subset which is not everything is nowhere dense. -/
@[ega "0 2.1.1" "partial"]
theorem isNowhereDense_of_isClosed_of_ne_univ {X : Type*} [TopologicalSpace X]
    [IrreducibleSpace X] {S : Set X} (hS : IsClosed S) (hne : S ≠ Set.univ) :
    IsNowhereDense S := by
  rw [IsNowhereDense, hS.closure_eq]
  by_contra h
  have hdense : Dense (interior S) :=
    isOpen_interior.dense (Set.nonempty_iff_ne_empty.2 h)
  apply hne
  rw [Set.eq_univ_iff_forall]
  intro x
  have : x ∈ closure (interior S) := hdense.closure_eq ▸ Set.mem_univ x
  have := closure_mono interior_subset this
  rwa [hS.closure_eq] at this

/-- **A closed subscheme which is not everything has smaller dimension.** For a closed immersion
`e : E ⟶ W` into an irreducible Noetherian scheme which is not surjective,
`dim E + 1 ≤ dim W`. -/
theorem topologicalKrullDim_add_one_le_of_isClosedImmersion {E W : AlgebraicGeometry.Scheme.{u}}
    (e : E ⟶ W) [AlgebraicGeometry.IsClosedImmersion e] [IrreducibleSpace W] [NoetherianSpace W]
    (he : ¬ Function.Surjective e) :
    topologicalKrullDim E + 1 ≤ topologicalKrullDim W := by
  have hemb := e.isClosedEmbedding
  rw [hemb.isEmbedding.toHomeomorph.isHomeomorph.topologicalKrullDim_eq]
  refine IsNowhereDense.topologicalKrullDim_add_one_le
    (isNowhereDense_of_isClosed_of_ne_univ hemb.isClosed_range fun h ↦ he ?_)
    hemb.isClosed_range
  exact Set.range_eq_univ.1 h

/-- **The fibres of a dominant morphism have smaller dimension.** Let `f : X ⟶ P` be dominant
and locally of finite type, with `X` irreducible, quasi-compact and Noetherian and `P` a Jacobson
scheme with at least two points. Then every fibre of `f` has dimension at most `dim X - 1`. -/
theorem topologicalKrullDim_fiber_add_one_le_of_isDominant {X P : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ P) [IrreducibleSpace X] [CompactSpace X] [NoetherianSpace X] [JacobsonSpace P]
    [AlgebraicGeometry.LocallyOfFiniteType f] [AlgebraicGeometry.IsDominant f]
    (hP : ¬ Subsingleton P) (t : P) :
    topologicalKrullDim (f.fiber t) + 1 ≤ topologicalKrullDim X := by
  rw [(f.fiberHomeo t).isHomeomorph.topologicalKrullDim_eq]
  by_cases ht : IsClosed ({t} : Set P)
  · have hS : IsClosed ((f : X → P) ⁻¹' {t}) := ht.preimage f.continuous
    refine IsNowhereDense.topologicalKrullDim_add_one_le
      (isNowhereDense_of_isClosed_of_ne_univ hS fun huniv ↦ hP ?_) hS
    have hrange : Set.range (f : X → P) ⊆ {t} := Set.range_subset_iff.2 fun x ↦
      (huniv ▸ Set.mem_univ x : x ∈ (f : X → P) ⁻¹' {t})
    have hcl : closure (Set.range (f : X → P)) = Set.univ :=
      (AlgebraicGeometry.Scheme.Hom.denseRange f).closure_eq
    have : (Set.univ : Set P) ⊆ {t} := by
      rw [← hcl]
      exact (closure_mono hrange).trans ht.closure_eq.le
    exact ⟨fun a b ↦ (this (Set.mem_univ a)).trans (this (Set.mem_univ b)).symm⟩
  · refine topologicalKrullDim_add_one_le_of_forall_specializes _ fun x hx ↦ ?_
    obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set X))).exists_closed_singleton
      ⟨x, subset_closure rfl⟩
    refine ⟨y, specializes_iff_mem_closure.2 hy, hyc, fun hyS ↦ ht ?_⟩
    exact (show f y = t from hyS) ▸ f.closedPoints_subset_preimage_closedPoints hyc

end Stacks.EtaleCohomology

end
