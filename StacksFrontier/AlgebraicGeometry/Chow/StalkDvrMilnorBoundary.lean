module

public import StacksFrontier.AlgebraicGeometry.Chow.DvrTameSymbol.MilnorTameSymbol
public import StacksFrontier.AlgebraicGeometry.Chow.StalkMilnorBoundary

/-!
# The tame-symbol boundary in every degree, at a discrete-valuation point of a scheme

Let `W` be an integral locally Noetherian scheme whose function field is identified with a field
`K` by a ring equivalence `e`. `Stacks.Chow.stalkMilnorBoundary` is the boundary

`∂_z : K^M_2(K) ⟶ K^M_1(κ(z))`

at a point `z` whose local ring is one-dimensional: the tame symbol of Stacks 02Q1, which exists
at every one-dimensional Noetherian local domain. This file does the same in every degree,

`∂_z : K^M_{i+1}(K) ⟶ K^M_i(κ(z))`,

**at a point whose local ring is a discrete valuation ring**, using
`Stacks.Chow.dvrMilnorTameSymbol'`; Stacks 0EAY constructs `∂_A` in higher degrees for a discrete
valuation ring `A`.

The family of boundaries is locally finite: on a quasi-compact open only finitely many
discrete-valuation points have nonzero boundary on a given class.

## Main definitions

* `Stacks.Chow.DvrPoint` — a point of `W` whose local ring is a discrete valuation ring.
* `Stacks.Chow.stalkDvrMilnorShift` — the boundary read on the whole Milnor K-ring.
* `Stacks.Chow.stalkDvrMilnorBoundary` — the boundary `∂_z : K^M_{i+1}(K) ⟶ K^M_i(κ(z))`.

## Main results

* `Stacks.Chow.stalkDvrMilnorShift_milnorKSymbolProd_eq_zero` — the boundary kills a symbol whose
  entries are units of the local ring.
* `Stacks.Chow.finite_stalkDvrMilnorBoundary_ne_zero` — local finiteness, in every degree.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
* [Stacks Project, Tag 02Q1](https://stacks.math.columbia.edu/tag/02Q1)
* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsDiscreteValuationRing

universe u

namespace Stacks.Chow

variable {W : Scheme.{u}} [IsIntegral W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K)

/-- A point of `W` whose local ring is a discrete valuation ring. -/
abbrev DvrPoint (W : Scheme.{u}) [IsIntegral W] : Type u :=
  {z : W // IsDiscreteValuationRing ↥(W.presheaf.stalk z)}

/-- A discrete-valuation point of `W` has coheight one. -/
theorem coheight_eq_one_of_dvrPoint (z : DvrPoint W) : Order.coheight (z : W) = 1 := by
  have := z.2
  have h : ((Order.coheight (z : W) : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (z : W),
      IsDiscreteValuationRing.ringKrullDim_eq_one]
    norm_num
  exact WithBot.coe_inj.mp h

/-! ### The boundary -/

/-- The tame-symbol boundary at a discrete-valuation point, read on the whole Milnor K-ring of
`K`: the coefficient of `ξ` of `Stacks.Chow.dvrMilnorShiftMap` at the local ring. -/
def stalkDvrMilnorShift (z : W) (hdvr : IsDiscreteValuationRing ↥(W.presheaf.stalk z)) :
    MilnorKRing K →+ MilnorKRing ↥(W.residueField z) :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  haveI := hdvr
  (MilnorKShift.shiftHom (IsLocalRing.ResidueField ↥(W.presheaf.stalk z))).comp
    (dvrMilnorShiftMap (A := ↥(W.presheaf.stalk z)) (F := K)
      (exists_irreducible ↥(W.presheaf.stalk z)).choose_spec).toAddMonoidHom

/-- **The tame-symbol boundary of Stacks 0EAY in every degree, at a discrete-valuation point of
`W`.** The local ring at `z` is a discrete valuation ring whose fraction field is `K`, so the
tame symbol of Stacks 0EAY is a homomorphism from the degree-`i + 1` Milnor K-group of `K` to the
degree-`i` Milnor K-group of the residue field at `z`. -/
def stalkDvrMilnorBoundary (z : W) (hdvr : IsDiscreteValuationRing ↥(W.presheaf.stalk z))
    (i : ℕ) : MilnorKTheory K (i + 1) →+ MilnorKTheory ↥(W.residueField z) i :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  haveI := hdvr
  dvrMilnorTameSymbol' ↥(W.presheaf.stalk z) K i

/-- The boundary `Stacks.Chow.stalkDvrMilnorBoundary` of a degree-`i + 1` class `α`, viewed in the
Milnor K-ring of the residue field, is `Stacks.Chow.stalkDvrMilnorShift` applied to `α`. -/
theorem coe_stalkDvrMilnorBoundary (z : W)
    (hdvr : IsDiscreteValuationRing ↥(W.presheaf.stalk z)) (i : ℕ)
    (α : MilnorKTheory K (i + 1)) :
    (stalkDvrMilnorBoundary e z hdvr i α : MilnorKRing ↥(W.residueField z)) =
      stalkDvrMilnorShift e z hdvr (α : MilnorKRing K) := rfl

/-! ### The boundary kills a symbol of units of the local ring -/

/-- **The boundary kills a symbol whose entries all come from units of the local ring.** -/
theorem stalkDvrMilnorShift_milnorKSymbolProd_eq_zero (z : W)
    (hdvr : IsDiscreteValuationRing ↥(W.presheaf.stalk z)) (l : List Kˣ)
    (hl : ∀ f ∈ l, ∃ u : ↥(W.presheaf.stalk z), IsUnit u ∧
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField u) = (f : K)) :
    stalkDvrMilnorShift e z hdvr (milnorKSymbolProd K l) = 0 := by
  let := stalkAlgebraOfFunctionFieldEquiv e z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  have := hdvr
  refine dvrMilnorShiftMap_shift_milnorKSymbolProd_eq_zero _ fun f hf ↦ ?_
  obtain ⟨_, ⟨u, rfl⟩, hue⟩ := hl f hf
  exact dvrFracOrd_eq_zero_of_eq_algebraMap_unit (u := u) _
    (by rwa [algebraMap_stalkAlgebraOfFunctionFieldEquiv e z])

/-! ### Units of the local rings along a list -/

/-- **Finitely many nonzero elements of `K` are simultaneously units of the local ring at every
point of some open set containing the generic point.** -/
theorem exists_isOpen_forall_forall_isUnit_stalk (l : List Kˣ) :
    ∃ O : W.Opens, genericPoint W ∈ (O : Set W) ∧ ∀ z ∈ (O : Set W), ∀ f ∈ l,
      ∃ u : ↥(W.presheaf.stalk z), IsUnit u ∧
        e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField u) = (f : K) := by
  induction l with
  | nil => exact ⟨⊤, by simp, by simp⟩
  | cons f l ih =>
      obtain ⟨O, hO, hOu⟩ := ih
      obtain ⟨Of, hOf, hOfu⟩ := exists_isOpen_forall_isUnit_stalk e (f : K) f.ne_zero
      refine ⟨Of ⊓ O, ⟨hOf, hO⟩, fun z hz g hg ↦ ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg
      · exact hOfu z hz.1
      · exact hOu z hz.2 g hg

/-! ### Local finiteness -/

variable [IsLocallyNoetherian W]

/-- **Local finiteness of the boundary of a symbol.** On a quasi-compact open only finitely many
discrete-valuation points have nonzero boundary on a given symbol. -/
theorem finite_stalkDvrMilnorShift_milnorKSymbolProd_ne_zero (V : W.Opens)
    (hV : IsCompact (V : Set W)) (l : List Kˣ) :
    {z : DvrPoint W | (z : W) ∈ (V : Set W) ∧
      stalkDvrMilnorShift e z.1 z.2 (milnorKSymbolProd K l) ≠ 0}.Finite := by
  obtain ⟨O, hO, hOu⟩ := exists_isOpen_forall_forall_isUnit_stalk e l
  have hfin := finite_coheight_eq_one_of_notMem_isOpen V O hV hO
  refine Set.Finite.of_finite_image (f := fun z : DvrPoint W ↦ (z : W)) (hfin.subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨z, ⟨hzV, hzne⟩, rfl⟩
  exact ⟨hzV, fun hzO ↦ hzne (stalkDvrMilnorShift_milnorKSymbolProd_eq_zero e z.1 z.2 l
    (hOu _ hzO)), coheight_eq_one_of_dvrPoint z⟩

/-- The additive subgroup of classes of `K^M_*(K)` whose boundary is nonzero at only finitely
many discrete-valuation points of an open `V`. -/
def stalkDvrMilnorBoundaryFinite (V : W.Opens) : AddSubgroup (MilnorKRing K) where
  carrier := {x | {z : DvrPoint W | (z : W) ∈ (V : Set W) ∧
    stalkDvrMilnorShift e z.1 z.2 x ≠ 0}.Finite}
  zero_mem' := Set.finite_empty.subset fun z hz ↦ hz.2 (map_zero _)
  add_mem' {x y} hx hy := (hx.union hy).subset fun z hz ↦ by
    by_cases h : stalkDvrMilnorShift e z.1 z.2 x = 0
    · exact Or.inr ⟨hz.1, fun hy ↦ hz.2 (by rw [map_add, h, hy, add_zero])⟩
    · exact Or.inl ⟨hz.1, h⟩
  neg_mem' {x} hx := hx.subset fun z hz ↦ ⟨hz.1, fun h ↦ hz.2 (by rw [map_neg, h, neg_zero])⟩

/-- **Local finiteness of the tame-symbol boundary in every degree.** Let `V` be a quasi-compact
open of the integral locally Noetherian scheme `W` and let `α` be a class of the degree-`i + 1`
Milnor K-group of `K`. Then only finitely many discrete-valuation points of `V` have nonzero
boundary `∂_z(α)`. -/
theorem finite_stalkDvrMilnorBoundary_ne_zero (V : W.Opens) (hV : IsCompact (V : Set W))
    (i : ℕ) (α : MilnorKTheory K (i + 1)) :
    {z : DvrPoint W | (z : W) ∈ (V : Set W) ∧
      stalkDvrMilnorBoundary e z.1 z.2 i α ≠ 0}.Finite := by
  have hmem : (α : MilnorKRing K) ∈ stalkDvrMilnorBoundaryFinite e V :=
    coe_mem_of_forall_milnorKSymbolProd_mem
      (fun l ↦ finite_stalkDvrMilnorShift_milnorKSymbolProd_ne_zero e V hV l) α
  refine (hmem : {z : DvrPoint W | (z : W) ∈ (V : Set W) ∧
    stalkDvrMilnorShift e z.1 z.2 (α : MilnorKRing K) ≠ 0}.Finite).subset fun z hz ↦ ?_
  refine ⟨hz.1, fun h ↦ hz.2 (Subtype.ext ?_)⟩
  rw [coe_stalkDvrMilnorBoundary, h]
  rfl

end Stacks.Chow

end
