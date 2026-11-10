module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.FullExactness
public import StacksFrontier.AlgebraicGeometry.Chow.StalkDvrMilnorBoundary
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Local

/-!
# The general tame symbol at a one-dimensional point of an integral scheme

Let `W` be an integral locally Noetherian scheme whose function field is identified with a field
`K` by a ring equivalence `e`. At a point `z` whose local ring `𝒪_{W,z}` is one-dimensional, that
local ring is a one-dimensional Noetherian local domain with fraction field `K`, so the tame
symbol of Stacks 0EAY built by normalization and norm
(`Stacks.Normalization.SemilocalDvrFamily.tameSymbol` at `Stacks.Chow.normalizationDvrFamily`) is
a homomorphism

`∂_z : K^M_{i+1}(K) → K^M_i(κ(z))`

in every degree. This file builds it and proves its **local finiteness**: for a class `α` and a
quasi-compact open `V`, only finitely many one-dimensional points `z ∈ V` have `∂_z(α) ≠ 0`.
The argument is the one of `Stacks.Chow.finite_stalkDvrMilnorBoundary_ne_zero`: a class is a sum
of symbols `{f_1, …, f_r}`, all entries of a symbol are units of the local rings on an open set
containing the generic point, the symbol of units dies under `∂_z`
(`Stacks.Normalization.SemilocalDvrFamily.tameShift_milnorKSymbolProd_eq_zero`), and a
quasi-compact open has only finitely many coheight-one points outside such an open set.

## Main definitions

* `Stacks.Chow.OneDimPoint` — the points with one-dimensional local ring.
* `Stacks.Chow.stalkTameShift` — `∂_z` on the whole Milnor K-ring.
* `Stacks.Chow.stalkTameSymbol` — `∂_z : K^M_{i+1}(K) → K^M_i(κ(z))`.

## Main results

* `Stacks.Chow.stalkTameShift_milnorKSymbolProd_eq_zero` — `∂_z` kills a symbol of local units.
* `Stacks.Chow.finite_stalkTameSymbol_ne_zero` — local finiteness.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W] {K : Type u} [Field K]
  (e : ↥W.functionField ≃+* K) (N : MilnorKNormFamily.{u})

/-- The points of `W` whose local ring is one-dimensional. -/
abbrev OneDimPoint (W : Scheme.{u}) : Type u :=
  {z : W // ringKrullDim (W.presheaf.stalk z) = 1}

omit [IsIntegral W] [IsLocallyNoetherian W] in
/-- A point with one-dimensional local ring has coheight one. -/
theorem coheight_eq_one_of_oneDimPoint (z : OneDimPoint W) : Order.coheight (z : W) = 1 := by
  have h : ((Order.coheight (z : W) : ℕ∞) : WithBot ℕ∞) = ((1 : ℕ∞) : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight (z : W), z.2]
    norm_num
  exact WithBot.coe_inj.mp h

/-- **The general tame symbol of Stacks 0EAY at a one-dimensional point of `W`**, on the whole
Milnor K-ring of `K`: the normalization-and-norm symbol of the one-dimensional Noetherian local
domain `𝒪_{W,z}`, whose fraction field is `K` through `e`. -/
def stalkTameShift (z : W) (hdim : ringKrullDim (W.presheaf.stalk z) = 1) :
    MilnorKRing K →+ MilnorKRing ↥(W.residueField z) :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  (normalizationDvrFamily ↥(W.presheaf.stalk z) K hdim).tameShift N

/-- **`∂_z` kills a symbol whose entries all come from units of the local ring.** -/
theorem stalkTameShift_milnorKSymbolProd_eq_zero (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) (l : List Kˣ)
    (hl : ∀ f ∈ l, ∃ u : ↥(W.presheaf.stalk z), IsUnit u ∧
      e (algebraMap ↥(W.presheaf.stalk z) ↥W.functionField u) = (f : K)) :
    stalkTameShift e N z hdim (milnorKSymbolProd K l) = 0 := by
  let := stalkAlgebraOfFunctionFieldEquiv e z
  have := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  refine Stacks.Normalization.SemilocalDvrFamily.tameShift_milnorKSymbolProd_eq_zero _ N
    fun f hf ↦ ?_
  obtain ⟨u, ⟨u', hu'⟩, hue⟩ := hl f hf
  refine ⟨u', ?_⟩
  rw [algebraMap_stalkAlgebraOfFunctionFieldEquiv e z, hu']
  exact hue

variable {N}

/-- **The general tame symbol of Stacks 0EAY at a one-dimensional point of `W`, in every
degree**: `∂_z : K^M_{i+1}(K) → K^M_i(κ(z))`. -/
def stalkTameSymbol (hN : N.PreservesGrading) (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) (i : ℕ) :
    MilnorKTheory K (i + 1) →+ MilnorKTheory ↥(W.residueField z) i :=
  letI := stalkAlgebraOfFunctionFieldEquiv e z
  haveI := isFractionRing_stalkAlgebraOfFunctionFieldEquiv e z
  (normalizationDvrFamily ↥(W.presheaf.stalk z) K hdim).tameSymbol hN i

/-- The degree-wise tame symbol `stalkTameSymbol`, viewed in the Milnor K-ring of `κ(z)`, is
`stalkTameShift` applied to the class viewed in the Milnor K-ring of `K`. -/
theorem coe_stalkTameSymbol (hN : N.PreservesGrading) (z : W)
    (hdim : ringKrullDim (W.presheaf.stalk z) = 1) (i : ℕ) (α : MilnorKTheory K (i + 1)) :
    (stalkTameSymbol e hN z hdim i α : MilnorKRing ↥(W.residueField z)) =
      stalkTameShift e N z hdim (α : MilnorKRing K) := rfl

variable (N)

/-- **Local finiteness of `∂` on a symbol.** -/
theorem finite_stalkTameShift_milnorKSymbolProd_ne_zero (V : W.Opens)
    (hV : IsCompact (V : Set W)) (l : List Kˣ) :
    {z : OneDimPoint W | (z : W) ∈ (V : Set W) ∧
      stalkTameShift e N z.1 z.2 (milnorKSymbolProd K l) ≠ 0}.Finite := by
  obtain ⟨O, hO, hOu⟩ := exists_isOpen_forall_forall_isUnit_stalk e l
  have hfin := finite_coheight_eq_one_of_notMem_isOpen V O hV hO
  refine Set.Finite.of_finite_image (f := fun z : OneDimPoint W ↦ (z : W)) (hfin.subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro _ ⟨z, ⟨hzV, hzne⟩, rfl⟩
  refine ⟨hzV, ?_, coheight_eq_one_of_oneDimPoint z⟩
  intro hzO
  exact hzne (stalkTameShift_milnorKSymbolProd_eq_zero e N z.1 z.2 l (hOu _ hzO))

/-- The classes of `K^M_*(K)` whose general tame symbol is nonzero at only finitely many
one-dimensional points of a quasi-compact open `V`: an additive subgroup. -/
def stalkTameShiftFinite (V : W.Opens) : AddSubgroup (MilnorKRing K) where
  carrier := {x | {z : OneDimPoint W | (z : W) ∈ (V : Set W) ∧
    stalkTameShift e N z.1 z.2 x ≠ 0}.Finite}
  zero_mem' := by
    refine Set.Finite.subset Set.finite_empty fun z hz ↦ ?_
    exact absurd (map_zero (stalkTameShift e N z.1 z.2)) hz.2
  add_mem' {x y} hx hy := by
    refine (hx.union hy).subset fun z hz ↦ ?_
    by_contra hcon
    refine hz.2 ?_
    rw [map_add]
    have h1 : stalkTameShift e N z.1 z.2 x = 0 := by
      by_contra h
      exact hcon (Or.inl ⟨hz.1, h⟩)
    have h2 : stalkTameShift e N z.1 z.2 y = 0 := by
      by_contra h
      exact hcon (Or.inr ⟨hz.1, h⟩)
    rw [h1, h2, add_zero]
  neg_mem' {x} hx := by
    refine hx.subset fun z hz ↦ ?_
    refine ⟨hz.1, ?_⟩
    intro h
    exact hz.2 (by rw [map_neg, h, neg_zero])

/-- **Local finiteness of the general tame symbol on the whole Milnor K-ring.** -/
theorem finite_stalkTameShift_ne_zero (V : W.Opens) (hV : IsCompact (V : Set W))
    (x : MilnorKRing K) :
    {z : OneDimPoint W | (z : W) ∈ (V : Set W) ∧ stalkTameShift e N z.1 z.2 x ≠ 0}.Finite := by
  have hmem : x ∈ stalkTameShiftFinite e N V :=
    mem_of_forall_milnorKSymbolProd_mem
      (fun l ↦ finite_stalkTameShift_milnorKSymbolProd_ne_zero e N V hV l) x
  exact hmem

variable {N}

/-- **Local finiteness of the general tame symbol of Stacks 0EAY in every degree.** Let `V` be a
quasi-compact open of `W` and `α` a class of `K^M_{i+1}(K)`. Then only finitely many points of
`V` with one-dimensional local ring have `∂_z(α) ≠ 0`. -/
theorem finite_stalkTameSymbol_ne_zero (hN : N.PreservesGrading) (V : W.Opens)
    (hV : IsCompact (V : Set W)) (i : ℕ) (α : MilnorKTheory K (i + 1)) :
    {z : OneDimPoint W | (z : W) ∈ (V : Set W) ∧
      stalkTameSymbol e hN z.1 z.2 i α ≠ 0}.Finite := by
  refine (finite_stalkTameShift_ne_zero e N V hV (α : MilnorKRing K)).subset fun z hz ↦ ?_
  refine ⟨hz.1, fun h ↦ hz.2 (Subtype.ext ?_)⟩
  rw [coe_stalkTameSymbol, h]
  rfl

end Stacks.Chow

end
