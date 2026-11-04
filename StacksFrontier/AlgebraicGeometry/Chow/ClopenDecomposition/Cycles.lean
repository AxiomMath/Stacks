module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.OpenPieceDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cycles decompose along a decomposition into open and closed pieces

Let `X` be a scheme locally of finite type over the base scheme of chapter 42 of the Stacks
Project, and let `X = \coprod_{i \in I} X_i` be a decomposition into open and closed subschemes,
i.e. a pairwise disjoint family of open subschemes covering `X`. Then

  `Z_k(X) = \prod_{i \in I} Z_k(X_i)`.

A cycle is a function on the points of `X` with locally finite support, supported on points of
delta-dimension `k`; restricting it to a piece gives such a function on that piece, because the
inclusion of an open subscheme is injective and open, and because delta-dimension is insensitive
to passing to an open subscheme (`Stacks.Chow.relativeDimension_opensι_comp`). Conversely a
family of cycles on the pieces glues, because every point of `X` lies in exactly one piece and
that piece is an open neighbourhood of it, so local finiteness is checked inside a single piece.

Notably the *gluing* direction uses only that the pieces are open, disjoint and cover; closedness
of the pieces is not needed for cycles (it is automatic anyway, see
`Stacks.Chow.IsClopenDecomposition.isClopen`). Where it is needed is one level up, for rational
equivalence: an integral closed subscheme of a piece is a closed subscheme of `X` only because
the piece is closed in `X`.

## Main definitions

* `Stacks.Chow.opensRestrictCycle` — the restriction of a cycle on `X` to an open subscheme.
* `Stacks.Chow.cycleGroupOpensRestrict` — that restriction as a homomorphism
  `Z_k(X) ⟶ Z_k(U)`; this is the projection map of the product decomposition.
* `Stacks.Chow.glueCycle` — the cycle on `X` glued from a family of cycles on the pieces of a
  decomposition.
* `Stacks.Chow.cycleGroupClopenEquiv` — the isomorphism `Z_k(X) ≅ ∏_i Z_k(X_i)`.

## Main results

* `Stacks.Chow.opensRestrictCycle_mem_cyclesOfDimension`,
  `Stacks.Chow.glueCycle_mem_cyclesOfDimension` — restriction and gluing preserve the grading by
  delta-dimension.
* `Stacks.Chow.cycleGroupClopenEquiv_apply`, `Stacks.Chow.cycleGroupClopenEquiv_symm_apply` — the
  two directions of the isomorphism, coefficientwise.

## Implementation notes

The index type `I` is allowed to live in any universe: the group of cycles on `X` lives in
`Type u` while the product over `I` lives in `Type (max u v)`, and `AddEquiv` is heterogeneous in
universes, so nothing is lost.

The projection `Stacks.Chow.cycleGroupOpensRestrict` is defined directly, as the restriction of
the coefficient function. The source describes it instead as flat pullback along the open
immersion `X_i → X`, which is flat and locally of finite type of relative dimension zero. The two
agree: `Stacks.Chow.cycleGroupOpensRestrict_eq_flatPullback` in
`StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback`. That identification is what
the criterion lemma of Stacks 02UC needs, since it is what makes capping with a bivariant class
commute with the projections; it is kept in a separate module so that this one, which is pure
cycle bookkeeping, does not depend on the construction of flat pullback.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u v

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Restricting a cycle to an open subscheme -/

/-- The restriction of a cycle on `X` to an open subscheme `U ⊆ X`: the coefficient at a point of
`U` is the coefficient at the corresponding point of `X`. -/
@[ega "IV 21.6.3" "more general"]
def opensRestrictCycle (U : X.Opens) (c : AlgebraicCycle X ℤ) :
    AlgebraicCycle (U : Scheme.{u}) ℤ where
  toFun z := c (U.ι.base z)
  supportWithinDomain' _ _ := trivial
  supportLocallyFiniteWithinDomain' z _ := by
    obtain ⟨t, ht, htfin⟩ := c.supportLocallyFiniteWithinDomain' (U.ι.base z) trivial
    refine ⟨U.ι.base ⁻¹' t, U.ι.continuous.continuousAt ht, ?_⟩
    refine Set.Finite.of_finite_image (f := U.ι.base) (htfin.subset ?_)
      U.isOpenEmbedding.injective.injOn
    rintro y ⟨w, ⟨hwt, hwne⟩, rfl⟩
    exact ⟨hwt, hwne⟩

/-- The coefficient of the restriction `opensRestrictCycle U c` at a point `z` of `U` is the
coefficient of `c` at the image of `z` in `X`. -/
@[simp]
theorem opensRestrictCycle_apply (U : X.Opens) (c : AlgebraicCycle X ℤ)
    (z : (U : Scheme.{u})) : opensRestrictCycle U c z = c (U.ι.base z) :=
  rfl

/-- The restriction of the zero cycle to an open subscheme is zero. -/
@[simp]
theorem opensRestrictCycle_zero (U : X.Opens) : opensRestrictCycle U 0 = 0 :=
  Function.locallyFinsuppWithin.ext fun _ ↦ rfl

/-- Restriction of cycles to an open subscheme is additive. -/
@[simp]
theorem opensRestrictCycle_add (U : X.Opens) (c d : AlgebraicCycle X ℤ) :
    opensRestrictCycle U (c + d) = opensRestrictCycle U c + opensRestrictCycle U d :=
  Function.locallyFinsuppWithin.ext fun _ ↦ rfl

/-- A cycle on an open subscheme `U` is a `k`-cycle exactly when its points of nonzero coefficient
have relative dimension `k` as points of `X`. -/
private theorem mem_cyclesOfDimension_opensι_comp_iff (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens) (k : ℤ) (g : AlgebraicCycle (U : Scheme.{u}) ℤ) :
    g ∈ cyclesOfDimension C (U.ι ≫ f) k ↔
      ∀ z, g z ≠ 0 → relativeDimension C.dimensionFunction f (U.ι.base z) = k := by
  simp_rw [mem_cyclesOfDimension_iff_forall_point, relativeDimension_opensι_comp]

/-- The restriction of a `k`-cycle to an open subscheme is a `k`-cycle. -/
theorem opensRestrictCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens) (k : ℤ) {c : AlgebraicCycle X ℤ}
    (hc : c ∈ cyclesOfDimension C f k) :
    opensRestrictCycle U c ∈ cyclesOfDimension C (U.ι ≫ f) k :=
  (mem_cyclesOfDimension_opensι_comp_iff C f U k _).mpr fun _ hz ↦
    (mem_cyclesOfDimension_iff_forall_point C f k c).mp hc _ hz

/-- The projection `Z_k(X) ⟶ Z_k(U)` onto the cycles of an open subscheme. For a piece of a
decomposition of `X` into open and closed subschemes this is the projection of the product
decomposition `Stacks.Chow.cycleGroupClopenEquiv`. -/
def cycleGroupOpensRestrict (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (U : X.Opens) (k : ℤ) : CycleGroup C f k →+ CycleGroup C (U.ι ≫ f) k where
  toFun c := ⟨opensRestrictCycle U c.1,
    opensRestrictCycle_mem_cyclesOfDimension C f U k c.2⟩
  map_zero' := Subtype.ext (opensRestrictCycle_zero U)
  map_add' c d := Subtype.ext (opensRestrictCycle_add U c.1 d.1)

/-- The coefficient of the projection `cycleGroupOpensRestrict C f U k c` at a point `z` of `U`
is the coefficient of `c` at the image of `z` in `X`. -/
@[simp]
theorem cycleGroupOpensRestrict_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (U : X.Opens) (k : ℤ) (c : CycleGroup C f k)
    (z : (U : Scheme.{u})) :
    (cycleGroupOpensRestrict C f U k c).1 z = c.1 (U.ι.base z) :=
  rfl

/-! ### Gluing a family of cycles on the pieces of a decomposition -/

variable {I : Type v} {U : I → X.Opens}

/-- The coefficient function of the cycle glued from a family of cycles on the pieces of a
decomposition: at a point `x` it is the coefficient of the cycle on the unique piece
containing `x`. -/
def glueCycleFun (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) (x : X) : ℤ :=
  g (h.index x) ⟨x, h.mem_index x⟩

/-- The glued coefficient function, computed inside any piece containing the point. -/
theorem glueCycleFun_apply_of_mem (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) {i : I} {x : X} (hx : x ∈ U i) :
    glueCycleFun h g x = g i ⟨x, hx⟩ := by
  obtain rfl : i = h.index x := (h.index_eq hx).symm
  rfl

/-- The glued coefficient function has locally finite support. -/
theorem glueCycleFun_locallyFiniteSupport (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) :
    LocallyFiniteSupport (glueCycleFun h g) := by
  intro x
  obtain ⟨t, ht, htfin⟩ :=
    (g (h.index x)).supportLocallyFiniteWithinDomain' ⟨x, h.mem_index x⟩ trivial
  refine ⟨(U (h.index x)).ι.base '' t,
    (U (h.index x)).isOpenEmbedding.isOpenMap.image_mem_nhds ht, ?_⟩
  refine (htfin.image (U (h.index x)).ι.base).subset ?_
  rintro y ⟨⟨w, hwt, rfl⟩, hyne⟩
  refine ⟨w, ⟨hwt, ?_⟩, rfl⟩
  have hw : glueCycleFun h g ((U (h.index x)).ι.base w) = g (h.index x) w :=
    glueCycleFun_apply_of_mem h g w.2
  exact fun hzero ↦ hyne (hw.trans hzero)

/-- The cycle on `X` glued from a family of cycles on the pieces of a decomposition of `X` into
open and closed subschemes. -/
def glueCycle (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) : AlgebraicCycle X ℤ where
  toFun := glueCycleFun h g
  supportWithinDomain' _ _ := trivial
  supportLocallyFiniteWithinDomain' x _ := glueCycleFun_locallyFiniteSupport h g x

/-- The coefficient of the glued cycle at a point `x` of the piece `U i` is the coefficient at
`x` of the cycle on `U i`. -/
@[simp]
theorem glueCycle_apply_of_mem (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) {i : I} {x : X} (hx : x ∈ U i) :
    glueCycle h g x = g i ⟨x, hx⟩ :=
  glueCycleFun_apply_of_mem h g hx

/-- Restricting a glued cycle to one of the pieces recovers the cycle on that piece. -/
@[simp]
theorem opensRestrictCycle_glueCycle (h : IsClopenDecomposition U)
    (g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ) (i : I) :
    opensRestrictCycle (U i) (glueCycle h g) = g i :=
  Function.locallyFinsuppWithin.ext fun z ↦ glueCycle_apply_of_mem h g z.2

/-- Gluing the restrictions of a cycle to the pieces recovers the cycle. -/
@[simp]
theorem glueCycle_opensRestrictCycle (h : IsClopenDecomposition U) (c : AlgebraicCycle X ℤ) :
    glueCycle h (fun i ↦ opensRestrictCycle (U i) c) = c :=
  Function.locallyFinsuppWithin.ext fun x ↦ glueCycle_apply_of_mem h _ (h.mem_index x)

/-- The glued cycle of a family of `k`-cycles is a `k`-cycle. -/
theorem glueCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    {g : ∀ i, AlgebraicCycle (U i : Scheme.{u}) ℤ}
    (hg : ∀ i, g i ∈ cyclesOfDimension C ((U i).ι ≫ f) k) :
    glueCycle h g ∈ cyclesOfDimension C f k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  rw [glueCycle_apply_of_mem h g (h.mem_index x)] at hx
  exact (mem_cyclesOfDimension_opensι_comp_iff C f _ k _).mp (hg _) ⟨x, h.mem_index x⟩ hx

/-! ### The product decomposition of the group of cycles -/

/-- **Cycles decompose along a decomposition into open and closed subschemes:**
`Z_k(X) = ∏_i Z_k(X_i)`, sending a cycle to the family of its restrictions to the pieces.

This is the decomposition of cycles used by the proofs of Stacks 0FDZ and Stacks 02UC. -/
def cycleGroupClopenEquiv (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (h : IsClopenDecomposition U) (k : ℤ) :
    CycleGroup C f k ≃+ ∀ i, CycleGroup C ((U i).ι ≫ f) k where
  toFun c i := cycleGroupOpensRestrict C f (U i) k c
  invFun g := ⟨glueCycle h fun i ↦ (g i).1,
    glueCycle_mem_cyclesOfDimension C f h k fun i ↦ (g i).2⟩
  left_inv c := Subtype.ext (glueCycle_opensRestrictCycle h c.1)
  right_inv g := funext fun i ↦
    Subtype.ext (opensRestrictCycle_glueCycle h (fun j ↦ (g j).1) i)
  map_add' c d := funext fun i ↦ (cycleGroupOpensRestrict C f (U i) k).map_add c d

/-- The component at `i` of the image of a cycle under `cycleGroupClopenEquiv` is its
restriction to the piece `U i`. -/
@[simp]
theorem cycleGroupClopenEquiv_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ) (c : CycleGroup C f k)
    (i : I) : cycleGroupClopenEquiv C f h k c i = cycleGroupOpensRestrict C f (U i) k c :=
  rfl

/-- The coefficient at a point `x` of `U i` of the cycle corresponding to a family `g` under
`cycleGroupClopenEquiv` is the coefficient of `g i` at `x`. -/
@[simp]
theorem cycleGroupClopenEquiv_symm_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (h : IsClopenDecomposition U) (k : ℤ)
    (g : ∀ i, CycleGroup C ((U i).ι ≫ f) k) {i : I} {x : X} (hx : x ∈ U i) :
    ((cycleGroupClopenEquiv C f h k).symm g).1 x = (g i).1 ⟨x, hx⟩ :=
  glueCycle_apply_of_mem h _ hx

end Stacks.Chow

end
