module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.Topology.Dimension.DimensionFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The vocabulary of Chow homology

Chapter 42 of the Stacks Project builds Chow homology over a base scheme `S` which is locally
Noetherian, universally catenary, and equipped with a dimension function `δ : S → ℤ`. This
file collects the basic objects of that setting: the base situation itself, the dimension
function it induces on any scheme locally of finite type over `S`, the graded pieces of the
group of cycles cut out by that dimension function, and proper pushforward of cycles.

A cycle on a scheme `X` is a locally finite formal sum `∑ n_Z [Z]` of integral closed
subschemes of `X`; Mathlib's `AlgebraicGeometry.AlgebraicCycle` is exactly this, indexing the
integral closed subscheme `closure {x}` by its generic point `x`. The delta-dimension of
`closure {x}` is `δ (f x) + trdeg_{κ(f x)} κ(x)` where `f : X ⟶ S` is the structure morphism,
and `Z_k(X)` is the subgroup of cycles whose coefficients are supported on points of
delta-dimension `k`. A proper morphism `f : X ⟶ Y` over `S` pushes `Z_k(X)` into `Z_k(Y)` by
weighting each component by the degree of its function-field extension when the
delta-dimension is preserved, and by zero otherwise; this is `AlgebraicCycle.map` for the pair
of relative dimension functions, and the content here is that it respects the grading.

## Main definitions

* `Stacks.Chow.relativeDimension` — the relative dimension function
  `x ↦ δ (f x) + trdeg_{κ(f x)} κ(x)` attached to a dimension function on the base (Stacks 02JW).
* `Stacks.Chow.ChowSituation` — the base scheme of chapter 42, bundled with its local
  Noetherianity, universal catenarity, and dimension function (Stacks 02QL).
* `Stacks.Chow.deltaDimension`, `Stacks.Chow.schemeDeltaDimension` — the delta-dimension of an
  irreducible closed subset, and of a whole scheme locally of finite type over the base
  (Stacks 02QP).
* `Stacks.Chow.cyclesOfDimension`, `Stacks.Chow.CycleGroup` — the subgroup `Z_k(X)` of cycles
  of delta-dimension `k`, and the corresponding type (Stacks 02QR).
* `Stacks.Chow.properPushforward` — proper pushforward of `k`-cycles (Stacks 02R4).

## Main results

* `Stacks.Chow.mem_cyclesOfDimension` — the grading condition, pointwise.
* `Stacks.Chow.map_mem_cyclesOfDimension` — `AlgebraicCycle.map` respects the grading.
* `Stacks.Chow.properPushforward_apply`, `Stacks.Chow.properPushforward_single` — the
  coefficient formula, and the value on a prime cycle.
* `Stacks.Chow.properPushforward_add`, `Stacks.Chow.properPushforward_zero` — additivity.
* `Stacks.Chow.schemeDeltaDimension_eq_genericPoint` — on an irreducible scheme the
  delta-dimension is the relative dimension of the generic point.
* `Stacks.Chow.deltaDimension_closure_singleton_of_coheight_one` — on an integral scheme of
  delta-dimension `n`, an integral closed subscheme of codimension one has delta-dimension
  `n - 1`, given a dimension function on `X` with underlying function `relativeDimension`.

## Implementation notes

The transcendence degree of a residue-field extension is cardinal-valued in Mathlib; under the
locally-finite-type hypothesis it is finite, and `Cardinal.toNat` is used to land in `ℤ`. The
algebra structure on the residue field of the source point is the one induced by
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`. Mathlib's `AlgebraicCycle` is Stacks' group of
cycles (tag 02QR): it is carried by `Function.locallyFinsupp`, and the equivalence between its
local finiteness of the *support* and Stacks' local finiteness of the *family of closed
subschemes* is `Stacks.Chow.locallyFinite_closure_singleton_iff`. `cyclesOfDimension` is an
`AddSubgroup` so that cycles of a fixed dimension inherit the group operations. The
delta-dimension of a whole scheme is valued in `EInt`, so that the empty supremum and an
unbounded family of component dimensions are both representable.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/


@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The relative dimension function -/

/-- The relative dimension attached to a dimension function `δ` on the base: at `x` it is the
base value at `f x` plus the transcendence degree of `κ(x)` over `κ(f x)`. -/
def relativeDimension {X S : Scheme.{u}} (δ : DimensionFunction S) (f : X ⟶ S) (x : X) : ℤ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  δ (f x) + (Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) : ℤ)

/-! ### The base situation -/

/-- The base situation of chapter 42: a locally Noetherian, universally catenary scheme equipped
with a dimension function on its underlying topological space. -/
@[stacks 02QL]
structure ChowSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The base scheme is locally Noetherian. -/
  [isLocallyNoetherian : IsLocallyNoetherian S]
  /-- The base scheme is universally catenary. -/
  isUniversallyCatenary : Scheme.IsUniversallyCatenary S
  /-- The chosen dimension function on the underlying topological space of the base scheme. -/
  dimensionFunction : DimensionFunction S

attribute [instance] ChowSituation.isLocallyNoetherian

/-! ### Delta-dimension -/

/-- The delta-dimension of an irreducible closed subset of a scheme locally of finite type over
the base is the value at its generic point of the dimension function propagated from the base. -/
@[stacks 02QP "irreducible closed subsets"]
def deltaDimension (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (Z : IrreducibleCloseds X) : ℤ :=
  relativeDimension C.dimensionFunction f Z.isIrreducible.genericPoint

/-- The delta-dimension may be evaluated at any generic point of the irreducible closed
subset. -/
theorem deltaDimension_eq_of_isGenericPoint (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (Z : IrreducibleCloseds X) (x : X)
    (hx : IsGenericPoint x (Z : Set X)) :
    deltaDimension C f Z = relativeDimension C.dimensionFunction f x :=
  congrArg _ ((Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq hx)

/-- The delta-dimension of a scheme locally of finite type over the base is the supremum of the
delta-dimensions of its irreducible components. In particular this defines the delta-dimension
of every closed subscheme of such a scheme. -/
@[stacks 02QP "closed subschemes"]
def schemeDeltaDimension (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] : EInt :=
  ⨆ Z : irreducibleComponents X,
    (deltaDimension C f ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set X) Z.2⟩ : EInt)

/-- The delta-dimension of a scheme is the supremum of the values on its irreducible
components. -/
theorem schemeDeltaDimension_eq_iSup (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] :
    schemeDeltaDimension C f =
      ⨆ Z : irreducibleComponents X,
        (deltaDimension C f
          ⟨Z, Z.2.1, isClosed_of_mem_irreducibleComponents (Z : Set X) Z.2⟩ : EInt) :=
  rfl

/-! ### Cycles of a fixed delta-dimension -/

/-- The subgroup `Z_k(X)` of cycles whose nonzero coefficients occur only at
integral closed subschemes of delta-dimension `k`. -/
@[stacks 02QR "k-cycles"]
def cyclesOfDimension (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : AddSubgroup (AlgebraicCycle X ℤ) where
  carrier := {c | ∀ Z : IrreducibleCloseds X,
    c Z.isIrreducible.genericPoint ≠ 0 → deltaDimension C f Z = k}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb Z h
    by_cases h' : a Z.isIrreducible.genericPoint = 0
    · exact hb Z (by simpa [h'] using h)
    · exact ha Z h'
  neg_mem' := by aesop

/-- A cycle belongs to `Z_k(X)` precisely when each integral closed subscheme occurring with a
nonzero coefficient has delta-dimension `k`. -/
@[simp]
theorem mem_cyclesOfDimension (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) (c : AlgebraicCycle X ℤ) :
    c ∈ cyclesOfDimension C f k ↔
      ∀ Z : IrreducibleCloseds X,
        c Z.isIrreducible.genericPoint ≠ 0 → deltaDimension C f Z = k :=
  Iff.rfl

/-- The abelian group `Z_k(X)` of cycles of delta-dimension `k`. -/
@[stacks 02QR "the abelian group of k-cycles"]
abbrev CycleGroup (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (k : ℤ) : Type u :=
  ↥(cyclesOfDimension C f k)

/-- The delta-dimension of the closure of a point of `X`, evaluated through
`deltaDimension`, is its relative dimension. -/
theorem deltaDimension_closure_singleton (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (x : X) :
    deltaDimension C f ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
      = relativeDimension C.dimensionFunction f x :=
  deltaDimension_eq_of_isGenericPoint C f _ x isGenericPoint_closure

/-- Membership in `Z_k(X)` read off at points rather than at irreducible closed subsets: a
cycle is a `k`-cycle exactly when every point carrying a nonzero coefficient has relative
dimension `k`. -/
theorem mem_cyclesOfDimension_iff_forall_point (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (c : AlgebraicCycle X ℤ) :
    c ∈ cyclesOfDimension C f k ↔
      ∀ x : X, c x ≠ 0 → relativeDimension C.dimensionFunction f x = k := by
  rw [mem_cyclesOfDimension]
  refine ⟨fun h x hx ↦ ?_, fun h Z hZ ↦ h _ hZ⟩
  set Z : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ with hZdef
  have hpt : Z.isIrreducible.genericPoint = x :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq
      (isGenericPoint_closure (x := x))
  have hZk := h Z (by rw [hpt]; exact hx)
  rwa [deltaDimension, hpt] at hZk

/-- For an irreducible scheme the delta-dimension is the relative dimension of the generic
point. -/
theorem schemeDeltaDimension_eq_genericPoint (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IrreducibleSpace X] :
    schemeDeltaDimension C p =
      (relativeDimension C.dimensionFunction p (genericPoint X) : EInt) := by
  have hW : (Set.univ : Set X) ∈ irreducibleComponents X := by
    simp [irreducibleComponents_eq_singleton]
  have : Subsingleton (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  rw [schemeDeltaDimension_eq_iSup, ciSup_subsingleton (⟨Set.univ, hW⟩ : irreducibleComponents X)]
  exact congrArg (fun z : ℤ => (z : EInt))
    (deltaDimension_eq_of_isGenericPoint C p _ (genericPoint X) (genericPoint_spec X))

/-- On an integral scheme of delta-dimension `n` over the base, an integral closed subscheme of
codimension one has delta-dimension `n - 1`, given a dimension function `d` on `X` with
underlying function `relativeDimension`. -/
theorem deltaDimension_closure_singleton_of_coheight_one (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) {x : X}
    (hx : Order.coheight x = 1) :
    deltaDimension C p
        ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩ = n - 1 := by
  have hlt : ∀ {a b : X}, a ≤ b → a ≠ b → a < b := fun hab hne ↦
    lt_iff_le_not_ge.mpr ⟨hab, fun h ↦ hne (Specializes.antisymm h hab).eq⟩
  have hηmax : Order.coheight (genericPoint X) = 0 :=
    Order.IsMax.coheight_eq_zero fun b _ ↦ genericPoint_specializes b
  have hxη : x ≠ genericPoint X := fun h ↦ by rw [h, hηmax] at hx; exact absurd hx (by decide)
  have himm : IsImmediateSpecialization (genericPoint X) x := by
    refine ⟨genericPoint_specializes x, Ne.symm hxη, fun z _ hzx ↦ ?_⟩
    by_cases hz : z = x
    · exact Or.inr hz
    refine Or.inl ?_
    have hstep : Order.coheight z + 1 ≤ 1 := by
      have hzx' := Order.coheight_add_one_le (hlt hzx (Ne.symm hz))
      rwa [hx] at hzx'
    by_contra hzη
    have hone : (1 : ℕ∞) ≤ Order.coheight z :=
      le_trans le_add_self (Order.coheight_add_one_le (hlt (genericPoint_specializes z) hzη))
    have habs : (2 : ℕ∞) ≤ 1 := by
      refine le_trans ?_ hstep
      rw [show (2 : ℕ∞) = 1 + 1 from rfl]
      gcongr
    exact absurd habs (by decide)
  have hη : d (genericPoint X) = n :=
    WithBotTop.coe_injective (by
      rw [hd]
      exact (schemeDeltaDimension_eq_genericPoint C p).symm.trans hn)
  have hdrop : d (genericPoint X) = d x + 1 := d.step_immediate himm
  rw [deltaDimension_closure_singleton, ← hd x]
  omega

/-! ### Proper pushforward -/

/-- The weighted pushforward of a `k`-cycle again has delta-dimension `k`. -/
theorem map_mem_cyclesOfDimension (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (_hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) :
    AlgebraicCycle.map f (relativeDimension C.dimensionFunction sX)
        (relativeDimension C.dimensionFunction sY) c.1 ∈ cyclesOfDimension C sY k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y hy
  simp only [AlgebraicCycle.map, Function.locallyFinsupp.map_apply] at hy
  obtain ⟨x, hxy, hterm⟩ := exists_ne_zero_of_finsum_mem_ne_zero hy
  simp only [AlgebraicCycle.mapCoeff] at hterm
  have hdimX : relativeDimension C.dimensionFunction sX x = k :=
    (mem_cyclesOfDimension_iff_forall_point C sX k c.1).mp c.2 x (mul_ne_zero_iff.mp hterm).1
  have hdimXY : relativeDimension C.dimensionFunction sX x =
      relativeDimension C.dimensionFunction sY (f.base x) := by
    by_contra h
    simp [h] at hterm
  rw [← hxy, ← hdimXY, hdimX]

/-- Proper pushforward of cycles of delta-dimension `k`. -/
@[stacks 02R4 "pushforward of cycles"]
def properPushforward (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) : CycleGroup C sX k → CycleGroup C sY k :=
  fun c ↦ ⟨AlgebraicCycle.map f (relativeDimension C.dimensionFunction sX)
    (relativeDimension C.dimensionFunction sY) c.1,
    map_mem_cyclesOfDimension C sX sY f hf k c⟩

/-- The coefficient of the proper pushforward at a point is the locally finite sum of the
coefficients above it, weighted by their residue-field degrees when the delta-dimension is
preserved. -/
@[stacks 02R4 "coefficient formula"]
theorem properPushforward_apply (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) (y : Y) :
    (properPushforward C sX sY f hf k c).1 y =
      ∑ᶠ x ∈ f.base ⁻¹' {y}, c.1 x *
        (if relativeDimension C.dimensionFunction sX x =
            relativeDimension C.dimensionFunction sY (f.base x)
          then (f.residueDegree x : ℤ) else 0) := by
  change AlgebraicCycle.map f (relativeDimension C.dimensionFunction sX)
      (relativeDimension C.dimensionFunction sY) c.1 y = _
  simp [AlgebraicCycle.map, AlgebraicCycle.mapCoeff]

/-- Proper pushforward respects sums of cycles. -/
theorem properPushforward_add (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (a b : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (a + b) =
      properPushforward C sX sY f hf k a + properPushforward C sX sY f hf k b := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  have hfin : ∀ c : AlgebraicCycle X ℤ, (f.base ⁻¹' {y} ∩ Function.support c).Finite := fun c ↦
    c.locallyFiniteSupport.finite_inter_support_of_isCompact
      (f.isProperMap.isCompact_preimage isCompact_singleton)
  simp only [AddSubgroup.coe_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply,
    properPushforward_apply, add_mul]
  exact finsum_mem_add_distrib' ((hfin a.1).subset fun x hx ↦ ⟨hx.1, (mul_ne_zero_iff.mp hx.2).1⟩)
    ((hfin b.1).subset fun x hx ↦ ⟨hx.1, (mul_ne_zero_iff.mp hx.2).1⟩)

/-- The zero cycle pushes forward to zero. -/
@[simp]
theorem properPushforward_zero (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) : properPushforward C sX sY f hf k 0 = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  simp [properPushforward, AlgebraicCycle.map, Function.locallyFinsupp.map,
    AlgebraicCycle.mapCoeff]

/-- An integral closed subscheme maps to its image with multiplicity the degree of the
function-field extension if its delta-dimension is preserved, and to zero otherwise. -/
@[stacks 02R4 "pushforward of an integral component"]
theorem properPushforward_single (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y) [IsProper f]
    (hf : f ≫ sY = sX) (k : ℤ) (x : X) (c : CycleGroup C sX k)
    (hc : c.1 = @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _ x (1 : ℤ)) :
    (properPushforward C sX sY f hf k c).1 =
      if relativeDimension C.dimensionFunction sY (f.base x) = k then
        @Function.locallyFinsuppWithin.single Y _ ℤ (Classical.decEq Y) _
          (f.base x) (f.residueDegree x : ℤ)
      else 0 := by
  classical
  have hx : relativeDimension C.dimensionFunction sX x = k := by
    refine (mem_cyclesOfDimension_iff_forall_point C sX k c.1).mp c.2 x ?_
    rw [hc]
    simp
  apply Function.locallyFinsuppWithin.ext
  intro y
  simp only [properPushforward, AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
  rw [hc]
  simp only [AlgebraicCycle.mapCoeff, Function.locallyFinsuppWithin.single_apply]
  rw [← finsum_set_coe_eq_finsum_mem]
  by_cases hy : y = f.base x
  · subst y
    rw [finsum_eq_single _ ⟨x, by simp⟩]
    · by_cases hd : relativeDimension C.dimensionFunction sY (f.base x) = k
      · simp [hx, hd, Function.locallyFinsuppWithin.single_apply]
      · have hd' : ¬ (k = relativeDimension C.dimensionFunction sY (f.base x)) :=
          fun h ↦ hd h.symm
        simp [hx, hd, hd']
    · intro z hz
      have hzx : (z : X) ≠ x := fun he ↦ hz (Subtype.ext he)
      simp [hzx]
  · have hxy : f.base x ≠ y := Ne.symm hy
    rw [finsum_eq_zero_of_forall_eq_zero]
    · by_cases hd : relativeDimension C.dimensionFunction sY (f.base x) = k
      · simp [hd, hxy.symm, Function.locallyFinsuppWithin.single_apply]
      · simp [hd]
    · intro z
      have hzx : (z : X) ≠ x := fun he ↦ hxy (by simpa [he] using z.2)
      simp [hzx]

/-- Proper pushforward along equal morphisms agrees. -/
public theorem properPushforward_hom_congr (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    {f g : X ⟶ Y} [IsProper f] [IsProper g] (hfg : f = g) (hf : f ≫ sY = sX)
    (hg : g ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sX sY f hf k c = properPushforward C sX sY g hg k c := by
  subst hfg
  exact Subtype.ext rfl


/-- The morphism `Y ×_S Z ⟶ X ×_S X` induced by `a : Y ⟶ X` and `b : Z ⟶ X`, over a bare base
scheme.  The pullback of the diagonal of `X` along it is `Y ×_X Z`, by
`CategoryTheory.Limits.pullbackDiagonalMapIdIso`. -/
public abbrev exteriorToSelfProductMap {S X Y Z : Scheme.{u}} (sX : X ⟶ S) (a : Y ⟶ X)
    (b : Z ⟶ X) :
    (CategoryTheory.Limits.pullback (a ≫ sX) (b ≫ sX) : Scheme.{u}) ⟶
      (CategoryTheory.Limits.pullback sX sX : Scheme.{u}) :=
  CategoryTheory.Limits.pullback.map (a ≫ sX) (b ≫ sX) sX sX a b (𝟙 _)
    (CategoryTheory.Category.comp_id _) (CategoryTheory.Category.comp_id _)

/-- A point of the spectrum of a local ring of `X` specializes, in `X`, to the point it localizes
at: the range of `AlgebraicGeometry.Scheme.fromSpecStalk` is the set of generizations of `x`,
which is `AlgebraicGeometry.Scheme.range_fromSpecStalk` of Mathlib (Stacks 01J7). -/
@[ega "I 2.4.2" "partial", ega "I 7.2.8" "partial"]
public theorem specializes_fromSpecStalk {X : Scheme.{u}} (x : X)
    (q : PrimeSpectrum (X.presheaf.stalk x)) : X.fromSpecStalk x q ⤳ x := by
  have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at h

end Stacks.Chow
