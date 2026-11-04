module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.CommuteOverDedekindBaseGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.AssociativityCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.PointClosureFlatProduct
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekindRepresentation

/-!
# The exterior product over a Dedekind base commutes with capping, over every base

Let `(S, δ)` be as in section 42.63 of the Stacks Project: `S` is locally Noetherian with an open
covering by spectra of Dedekind domains, `δ = 0` at closed points and `δ = 1` elsewhere. A field
is a Dedekind domain, so `S` may have zero-dimensional components; they form the open and closed
zero-dimensional locus `S₀`. Let `X` be locally of finite type over `S` and `α ∈ CH_n(X)`, let
`Y ⟶ Z` be a morphism of schemes locally of finite type over `S` and `c' ∈ A^q(Y ⟶ Z)`.
**Stacks 0FC7** asserts

  `α × (c' ∩ β) = c' ∩ (α × β)`

for `β` a Chow class on a test scheme over `Z`, the exterior product being that of Stacks 0FC4.

The source takes the class `c_α ∈ A^{1-n}(X ⟶ S)` with `c_α ∩ α' = α × α'` and applies
Stacks 0FC6 to `c_α` and `c'`. Over a zero-dimensional component of the base such a class need not
exist as stated, but there the exterior product vanishes: for a point `x` over `S₀` the closure
of `x` is flat over the point it lies over, the product `closure {x} ×_S closure {y}` has
delta-dimension `δ(x) + δ(y)`, and its cycle in delta-dimension `δ(x) + δ(y) - 1` is zero
(`Stacks.Chow.exteriorProductDedekindCycles_eq_zero_of_mem_zeroDimensionalLocus_left`). So `α` is
split as `α = c ∩ [S]₁ + α₀` with `α₀` supported over `S₀` and `c ∩ [S₀]₀ = 0`, where `[S₀]₀` is
the fundamental class of `S₀`; the class `c` acts by exterior product with `c ∩ [S]₁`, and the
part `α₀` contributes zero to both sides.

## Main results

* `Stacks.Chow.exteriorProductDedekindChow_cap_comm_of_isDedekindChowBase` — **Stacks 0FC7**, over
  every base as in section 42.63.
* `Stacks.Chow.isExteriorProductOverBase_of_bivariantCapZeroDimensionalLocus_eq_zero`
  — a class `c ∈ A^p(X ⟶ S)` with `c ∩ [S₀]₀ = 0` acts by exterior product with `c ∩ [S]₁`.
* `Stacks.Chow.exists_bivariantCapBaseFundamentalClass_add_mk_eq` — every `α ∈ CH_{1-p}(X)` is
  `c ∩ [S]₁ + [a₀]` for such a class `c` and a cycle `a₀` supported over `S₀`.
* `Stacks.Chow.exteriorProductDedekindChow_mk_eq_zero_of_mem_zeroDimensionalLocus` — the exterior
  product with a cycle supported over `S₀` vanishes.

## Implementation notes

The class `c_α` of the source is replaced by the pair `(c, a₀)` of
`Stacks.Chow.exists_bivariantCapBaseFundamentalClass_add_mk_eq`. A class `c` acting by exterior
product with an `α` having nonzero part over `S₀` does not exist in general: for `S = Spec k` with
`δ = 0` the exterior product is identically zero while `c ∩ [S₀]₀` can be any class. Requiring
`c ∩ [S₀]₀ = 0` is what makes `c` act by exterior product, the exterior product with the
fundamental class of an integral scheme over `S₀` being zero.

For a test scheme dominating a one-dimensional component the computation is
`Stacks.Chow.cap_fundamentalCycle_heq_of_mem_genericPoints_of_dimensionFunction_eq_one`, which
needs only `δ = 1` at the image of the generic point of the test scheme.

## References

* [Stacks Project, Tag 0FC7](https://stacks.math.columbia.edu/tag/0FC7)
* [Stacks Project, Tag 0FC6](https://stacks.math.columbia.edu/tag/0FC6)
* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Tag 0FC4](https://stacks.math.columbia.edu/tag/0FC4)
* [Stacks Project, Section 42.63 (Tag 0FC3)](https://stacks.math.columbia.edu/tag/0FC3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The exterior product over the zero-dimensional locus -/

section Vanishing

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (g : Y ⟶ C.S) [LocallyOfFiniteType g] {n m : ℤ}

omit [LocallyOfFiniteType f] in
/-- A point lying over the zero-dimensional locus of a base as in section 42.63 dominates an
irreducible component of the base, namely the point it lies over. -/
theorem dominatesBaseComponent_of_mem_zeroDimensionalLocus (hS : IsDedekindChowBase C) {x : X}
    (hx : f.base x ∈ zeroDimensionalLocus C) : DominatesBaseComponent C f x :=
  ((hS.mem_zeroDimensionalLocus_iff).1 hx).2

/-- A term of the exterior product vanishes once the coefficient of the product of the closures
vanishes in delta-dimension `n + m - 1` for the relative dimensions of the two points. -/
private theorem exteriorProductDedekindTerm_eq_zero_of_coeff_eq_zero (a : CycleGroup C f n)
    (b : CycleGroup C g m) (z : (pullback f g : Scheme.{u})) (x : X) (y : Y)
    (h : relativeDimension C.dimensionFunction f x = n →
      relativeDimension C.dimensionFunction g y = m →
      closedSubschemeCycleCoeff C (pullback.fst f g ≫ f)
        (exteriorProductIdeal f g x y).subschemeι (n + m - 1) z = 0) :
    exteriorProductDedekindTerm C f g n m a b z (x, y) = 0 := by
  classical
  unfold exteriorProductDedekindTerm
  dsimp only
  split_ifs
  · by_cases ha : a.1 x = 0
    · rw [ha, zero_mul, zero_mul]
    by_cases hb : b.1 y = 0
    · rw [hb, mul_zero, zero_mul]
    rw [h ((mem_cyclesOfDimension_iff_forall_point C f n a.1).1 a.2 x ha)
      ((mem_cyclesOfDimension_iff_forall_point C g m b.1).1 b.2 y hb), mul_zero]
  · rfl

/-- Over a base as in section 42.63, a pair of components whose first entry lies over the
zero-dimensional locus contributes nothing to the exterior product: the product of the two
closures has delta-dimension `n + m`, so its cycle in delta-dimension `n + m - 1` vanishes. -/
theorem exteriorProductDedekindTerm_eq_zero_of_mem_zeroDimensionalLocus_left
    (hS : IsDedekindChowBase C) (a : CycleGroup C f n) (b : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) {x : X} (hx : f.base x ∈ zeroDimensionalLocus C) (y : Y) :
    exteriorProductDedekindTerm C f g n m a b z (x, y) = 0 :=
  exteriorProductDedekindTerm_eq_zero_of_coeff_eq_zero f g a b z x y fun hxn hym ↦
    closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_left hS f g x y
      (dominatesBaseComponent_of_mem_zeroDimensionalLocus f hS hx) hx.2 (n + m - 1)
      (by omega) z

/-- Over a base as in section 42.63, a pair of components whose second entry lies over the
zero-dimensional locus contributes nothing to the exterior product. -/
theorem exteriorProductDedekindTerm_eq_zero_of_mem_zeroDimensionalLocus_right
    (hS : IsDedekindChowBase C) (a : CycleGroup C f n) (b : CycleGroup C g m)
    (z : (pullback f g : Scheme.{u})) (x : X) {y : Y} (hy : g.base y ∈ zeroDimensionalLocus C) :
    exteriorProductDedekindTerm C f g n m a b z (x, y) = 0 :=
  exteriorProductDedekindTerm_eq_zero_of_coeff_eq_zero f g a b z x y fun hxn hym ↦
    closedSubschemeCycleCoeff_product_eq_zero_of_isClosed_right hS f g x y
      (dominatesBaseComponent_of_mem_zeroDimensionalLocus g hS hy) hy.2 (n + m - 1)
      (by omega) z

/-- The exterior product of two cycles vanishes if every term whose two coefficients are nonzero
does. -/
private theorem exteriorProductDedekindCycles_eq_zero_of_term_eq_zero (a : CycleGroup C f n)
    (b : CycleGroup C g m)
    (h : ∀ (z : (pullback f g : Scheme.{u})) (q : X × Y), a.1 q.1 ≠ 0 → b.1 q.2 ≠ 0 →
      exteriorProductDedekindTerm C f g n m a b z q = 0) :
    exteriorProductDedekindCycles C f g n m a b = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [exteriorProductDedekindCycles_apply]
  refine finsum_eq_zero_of_forall_eq_zero fun q ↦ ?_
  by_cases ha : a.1 q.1 = 0
  · unfold exteriorProductDedekindTerm
    split_ifs
    · rw [ha, zero_mul, zero_mul]
    · rfl
  by_cases hb : b.1 q.2 = 0
  · unfold exteriorProductDedekindTerm
    split_ifs
    · rw [hb, mul_zero, zero_mul]
    · rfl
  exact h z q ha hb

/-- **The exterior product with a cycle supported over the zero-dimensional locus vanishes**, over
a base as in section 42.63. -/
theorem exteriorProductDedekindCycles_eq_zero_of_mem_zeroDimensionalLocus_left
    (hS : IsDedekindChowBase C) (a : CycleGroup C f n)
    (ha : ∀ x, a.1 x ≠ 0 → f.base x ∈ zeroDimensionalLocus C) (b : CycleGroup C g m) :
    exteriorProductDedekindCycles C f g n m a b = 0 :=
  exteriorProductDedekindCycles_eq_zero_of_term_eq_zero f g a b fun z q hq _ ↦
    exteriorProductDedekindTerm_eq_zero_of_mem_zeroDimensionalLocus_left f g hS a b z
      (ha _ hq) q.2

/-- **The exterior product with a cycle supported over the zero-dimensional locus vanishes**, in
the second variable, over a base as in section 42.63. -/
theorem exteriorProductDedekindCycles_eq_zero_of_mem_zeroDimensionalLocus_right
    (hS : IsDedekindChowBase C) (a : CycleGroup C f n) (b : CycleGroup C g m)
    (hb : ∀ y, b.1 y ≠ 0 → g.base y ∈ zeroDimensionalLocus C) :
    exteriorProductDedekindCycles C f g n m a b = 0 :=
  exteriorProductDedekindCycles_eq_zero_of_term_eq_zero f g a b fun z q _ hq ↦
    exteriorProductDedekindTerm_eq_zero_of_mem_zeroDimensionalLocus_right f g hS a b z q.1
      (hb _ hq)

/-- **The exterior product of Chow classes with the class of a cycle supported over the
zero-dimensional locus vanishes**, over a base as in section 42.63. -/
theorem exteriorProductDedekindChow_mk_eq_zero_of_mem_zeroDimensionalLocus
    (hS : IsDedekindChowBase C) (hfac : ExteriorProductFactorsThroughRationalEquivalence C f g n m)
    (a : CycleGroup C f n) (ha : ∀ x, a.1 x ≠ 0 → f.base x ∈ zeroDimensionalLocus C) :
    exteriorProductDedekindChow C f g n m hfac
      (QuotientAddGroup.mk' (rationalEquivalences C f n) a) = 0 := by
  refine AddMonoidHom.ext fun β ↦ ?_
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C g m) β
  rw [exteriorProductDedekindChow_mk_mk,
    exteriorProductDedekindCycles_eq_zero_of_mem_zeroDimensionalLocus_left f g hS a ha b,
    map_zero, AddMonoidHom.zero_apply]

end Vanishing

/-! ### The classes acting by exterior product -/

section Representation

variable {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (p : ℤ)

/-- **A class killing `[S₀]₀` acts by exterior product with its image.** Over a base as in
section 42.63, a class `c ∈ A^p(X → S)` with `c ∩ [S₀]₀ = 0`, `S₀` the zero-dimensional locus,
caps as the exterior product with `c ∩ [S]₁`:

  `c ∩ α' = (c ∩ [S]₁) × α'`

for every scheme `U` locally of finite type over the base and every `α' ∈ CH_k(U)`.

It suffices to check this on the fundamental class of an integral `T`
(`Stacks.Chow.cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral`). If `T` lies over `S₀`
both sides vanish, the left one because `c` kills `[S₀]₀`
(`Stacks.Chow.cap_fundamentalChowClass_eq_zero_of_mem_zeroDimensionalLocus`) and the right one
for dimension reasons. If `T` dominates a one-dimensional component, `[T]` is a flat pullback of
`[S]₁`; otherwise `T` lies over a closed point with a proper generalization and
`Stacks.Chow.cap_fundamentalCycle_heq_of_notMem_genericPoints` applies. -/
theorem isExteriorProductOverBase_of_bivariantCapZeroDimensionalLocus_eq_zero
    (hS : IsDedekindChowBase C)
    (c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p)
    (hc : bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p c = 0) :
    IsExteriorProductOverBase C (gysinSystemOfInvertible C) sX (1 - p) p
      (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c) c := by
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX (1 - p))
    (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c)
  intro U u _ k hfac α'
  induction α' using QuotientAddGroup.induction_on with
  | H b =>
  rw [← ha]
  refine cap_heq_exteriorProductDedekindCycles_of_forall_isIntegral C _ sX (1 - p) p c a rfl
    (fun t _ _ l ↦ ?_) u k b
  by_cases h0 : t.base (genericPoint _) ∈ zeroDimensionalLocus C
  · have hcap := cap_fundamentalChowClass_eq_zero_of_mem_zeroDimensionalLocus _ sX p hS c hc t h0 l
    rw [← chowGroupCongr_fundamentalChowClass C (Category.comp_id t).symm l] at hcap
    have hext : exteriorProductDedekindCycles C sX t (1 - p) l a (fundamentalCycle C t l) = 0 :=
      exteriorProductDedekindCycles_eq_zero_of_mem_zeroDimensionalLocus_right sX t hS a _
        fun y _ ↦ by
          rw [eq_of_specializes_of_mem_zeroDimensionalLocus h0
            (((genericPoint_spec _).specializes (Set.mem_univ y)).map t.continuous)]
          exact h0
    refine HEq.trans (heq_of_eq hcap) ?_
    rw [hext, map_zero]
    exact heq_zero_chowGroup_of_degree_eq C _ (by ring)
  by_cases hgen : t.base (genericPoint _) ∈ genericPoints C.S
  · exact cap_fundamentalCycle_heq_of_mem_genericPoints_of_dimensionFunction_eq_one _ sX p hS c a
      ha.symm t hgen (hS.dimensionFunction_eq_one_of_notMem_zeroDimensionalLocus hgen h0) l
  · exact cap_fundamentalCycle_heq_of_notMem_genericPoints sX p hS c a ha.symm t hgen l

omit [LocallyOfFiniteType sX] in
/-- The parts of `X` over the positive-dimensional and the zero-dimensional loci of a base as in
section 42.63 decompose `X` into two open and closed subschemes. -/
theorem isClopenDecomposition_preimage_zeroDimensionalLocus (hS : IsDedekindChowBase C) :
    IsClopenDecomposition fun i : ULift.{u} Bool ↦
      cond i.down (sX ⁻¹ᵁ hS.positiveDimensionalLocus) (sX ⁻¹ᵁ zeroDimensionalLocus C) := by
  have hdisj : Disjoint (sX ⁻¹ᵁ hS.positiveDimensionalLocus) (sX ⁻¹ᵁ zeroDimensionalLocus C) :=
    TopologicalSpace.Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun _ h1 h2 ↦ h1 h2)
  refine ⟨fun i j hij ↦ ?_, eq_top_iff.mpr fun x _ ↦ ?_⟩
  · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · exact absurd rfl hij
    · exact hdisj.symm
    · exact hdisj
    · exact absurd rfl hij
  · rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : sX.base x ∈ zeroDimensionalLocus C
    · exact ⟨⟨false⟩, h⟩
    · exact ⟨⟨true⟩, h⟩

/-- **Every Chow class is an image of Stacks 0FC5 up to a class supported over `S₀`.** Over a
base as in section 42.63, every `α ∈ CH_{1-p}(X)` is `c ∩ [S]₁ + [a₀]` for a class
`c ∈ A^p(X → S)` with `c ∩ [S₀]₀ = 0` and a cycle `a₀` supported over the zero-dimensional locus
`S₀`.

Split a cycle `a` representing `α` as `(a - a₀) + a₀` along the decomposition of `X` into its
parts over `S₀` and over its complement. A class `d₁` with `d₁ ∩ [S]₁ = [a - a₀]` exists, both
sides vanishing over `S₀` and the images of bivariant classes reaching every class away from it
(`Stacks.Chow.exists_mem_centralOverBaseSubgroup_restrict_eq`); subtracting a class `d₀` with
`d₀ ∩ [S]₁ = 0` and `d₀ ∩ [S₀]₀ = d₁ ∩ [S₀]₀`
(`Stacks.Chow.exists_mem_centralOverBaseSubgroup_bivariantCapZeroDimensionalLocus_eq`) gives
`c = d₁ - d₀`. -/
theorem exists_bivariantCapBaseFundamentalClass_add_mk_eq (hS : IsDedekindChowBase C)
    (α : chowGroup C sX (1 - p)) :
    ∃ c : BivariantClass C (gysinSystemOfInvertible C) sX (𝟙 C.S) sX (Category.comp_id sX) p,
      bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p c = 0 ∧
        ∃ a₀ : CycleGroup C sX (1 - p),
          (∀ x, a₀.1 x ≠ 0 → sX.base x ∈ zeroDimensionalLocus C) ∧
            bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p c +
              QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a₀ = α := by
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX (1 - p)) α
  let UX : ULift.{u} Bool → X.Opens := fun i ↦
    cond i.down (sX ⁻¹ᵁ hS.positiveDimensionalLocus) (sX ⁻¹ᵁ zeroDimensionalLocus C)
  have hUX : IsClopenDecomposition UX := isClopenDecomposition_preimage_zeroDimensionalLocus sX hS
  have hP : IsClopenDecomposition fun i ↦ (UX i).ι.opensRange := by
    simpa only [Scheme.Opens.opensRange_ι] using hUX
  -- the part of `a` over the zero-dimensional locus
  let a₀ : CycleGroup C sX (1 - p) := (cycleGroupClopenEquiv C sX hUX (1 - p)).symm
    fun i ↦ cond i.down 0 (cycleGroupOpensRestrict C sX (UX i) (1 - p) a)
  have ha₀0 : ∀ x, sX.base x ∈ zeroDimensionalLocus C → a₀.1 x = a.1 x := fun x hx ↦
    (cycleGroupClopenEquiv_symm_apply C sX hUX (1 - p) _ (i := ⟨false⟩) hx).trans rfl
  have ha₀1 : ∀ x, sX.base x ∉ zeroDimensionalLocus C → a₀.1 x = 0 := fun x hx ↦
    (cycleGroupClopenEquiv_symm_apply C sX hUX (1 - p) _ (i := ⟨true⟩) hx).trans rfl
  have hres0 : ∀ (V : X.Opens) (b : CycleGroup C sX (1 - p)), (∀ z : V, b.1 (V.ι.base z) = 0) →
      chowGroupRestrict C sX (V.ι ≫ sX) V.ι rfl (1 - p)
        (QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) b) = 0 := by
    intro V b hb
    have h : cycleGroupRestrict C sX (V.ι ≫ sX) V.ι rfl (1 - p) b = 0 :=
      Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ hb z)
    rw [chowGroupRestrict_mk, h, map_zero]
  -- a class reaching `a - a₀`
  obtain ⟨d₁, -, h₁⟩ := exists_mem_centralOverBaseSubgroup_restrict_eq C sX p hS
    (QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) a)
  have hΦ₁ : bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p d₁ =
      QuotientAddGroup.mk' (rationalEquivalences C sX (1 - p)) (a - a₀) := by
    refine (chowGroupClopenRestrictEquiv C sX (fun i ↦ (UX i).ι ≫ sX) (fun i ↦ (UX i).ι)
      (fun _ ↦ rfl) hP (1 - p)).injective (funext fun i ↦ ?_)
    rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
    rcases i with ⟨_ | _⟩
    · refine (chowGroupRestrict_bivariantCapBaseFundamentalClass_eq_zero _ sX p hS d₁).trans
        (hres0 (UX ⟨false⟩) _ fun z ↦ ?_).symm
      show a.1 _ - a₀.1 _ = 0
      rw [ha₀0 ((UX ⟨false⟩).ι.base z) z.2, sub_self]
    · refine h₁.trans ?_
      rw [map_sub, map_sub, hres0 (UX ⟨true⟩) a₀ fun z ↦ ha₀1 _ z.2, sub_zero]
      rfl
  obtain ⟨d₀, -, hd₀1, hd₀0⟩ :=
    exists_mem_centralOverBaseSubgroup_bivariantCapZeroDimensionalLocus_eq C sX hS p
      (bivariantCapZeroDimensionalLocus C (gysinSystemOfInvertible C) sX p d₁)
  refine ⟨d₁ - d₀, by rw [map_sub, hd₀0, sub_self], a₀, fun x hx ↦ ?_, ?_⟩
  · by_contra h
    exact hx (ha₀1 x h)
  · rw [map_sub, hΦ₁, hd₀1, sub_zero, map_sub, sub_add_cancel]

end Representation

/-! ### Stacks 0FC7 -/

section Main

variable {C : ChowSituation.{u}}

/-- **Stacks 0FC7.** Let `(S, δ)` be as in section 42.63 of the Stacks Project, let `X` be locally
of finite type over `S` and `α ∈ CH_n(X)`, let `Y ⟶ Z` be a morphism of schemes locally of finite
type over `S` and `c' ∈ A^q(Y ⟶ Z)`. Then for every test scheme `t : T ⟶ Z` and `β ∈ CH_m(T)`,

  `α × (c' ∩ β) = c' ∩ (α × β)`

on `X ×_S Y ×_Z T`, the two iterated fibre products being compared through
`Stacks.Chow.mixedCommuteHom`, the exterior product being that of Stacks 0FC4.

Write `α = c ∩ [S]₁ + [a₀]` with `c ∩ [S₀]₀ = 0` and `a₀` supported over the zero-dimensional
locus (`Stacks.Chow.exists_bivariantCapBaseFundamentalClass_add_mk_eq`). The exterior product with
`[a₀]` vanishes, `c` acts by exterior product with `c ∩ [S]₁`, and `c` commutes with `c'` by
Stacks 0FC6 (`Stacks.Chow.bivariantCommuteOverBase_of_isDedekindChowBase_general`), so
`Stacks.Chow.exteriorProductDedekindChow_cap_comm` applies. -/
@[stacks 0FC7 "the whole statement α × (c' ∩ β) = c' ∩ (α × β), at every test scheme T → Z, for \
every base as in section 42.63, including bases with zero-dimensional components (spectra of \
fields), for the bivariant classes of the Gysin system of invertible modules \
`Stacks.Chow.gysinSystemOfInvertible`; the exterior product is that of Stacks 0FC4, its descent \
discharged by `Stacks.Chow.IsDedekindChowBase.exteriorProductFactorsThroughRationalEquivalence`"]
theorem exteriorProductDedekindChow_cap_comm_of_isDedekindChowBase (hS : IsDedekindChowBase C)
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sZ : Z ⟶ C.S)
    [LocallyOfFiniteType sZ] (w : Y ⟶ Z) [LocallyOfFiniteType w] (n q : ℤ) (α : chowGroup C sX n)
    (c' : BivariantClass C (gysinSystemOfInvertible C) (w ≫ sZ) sZ w rfl q)
    {T : Scheme.{u}} (t : T ⟶ Z) [LocallyOfFiniteType t] (m : ℤ) (β : chowGroup C (t ≫ sZ) m) :
    chowPushforwardOfIso C (pullback.fst sX (pullback.fst w t ≫ (w ≫ sZ)) ≫ sX)
        (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
        (mixedCommuteHom sX sZ w t) (mixedCommuteHom_comp_structureMorphism sX sZ w t)
        (n + (m - q) - 1)
        (exteriorProductDedekindChow C sX (pullback.fst w t ≫ (w ≫ sZ)) n (m - q)
          (hS.exteriorProductFactorsThroughRationalEquivalence sX _ n (m - q)) α
          (c'.cap t m β)) =
      chowGroupDegreeEquiv C (pullback.fst w (pullback.snd sX (t ≫ sZ) ≫ t) ≫ (w ≫ sZ))
        (by ring : (n + m - 1) - q = n + (m - q) - 1)
        (c'.cap (pullback.snd sX (t ≫ sZ) ≫ t) (n + m - 1)
          (chowGroupCongr C
            (by rw [Category.assoc]; exact pullback.condition (f := sX) (g := t ≫ sZ))
            (n + m - 1) (exteriorProductDedekindChow C sX (t ≫ sZ) n m
              (hS.exteriorProductFactorsThroughRationalEquivalence sX (t ≫ sZ) n m) α β))) := by
  obtain ⟨p, rfl⟩ : ∃ p, n = 1 - p := ⟨1 - n, by ring⟩
  obtain ⟨c, hc, a₀, ha₀, rfl⟩ := exists_bivariantCapBaseFundamentalClass_add_mk_eq sX p hS α
  have hY := exteriorProductDedekindChow_mk_eq_zero_of_mem_zeroDimensionalLocus sX
    (pullback.fst w t ≫ (w ≫ sZ)) hS
    (hS.exteriorProductFactorsThroughRationalEquivalence sX _ (1 - p) (m - q)) a₀ ha₀
  have hT := exteriorProductDedekindChow_mk_eq_zero_of_mem_zeroDimensionalLocus sX (t ≫ sZ) hS
    (hS.exteriorProductFactorsThroughRationalEquivalence sX (t ≫ sZ) (1 - p) m) a₀ ha₀
  rw [map_add, AddMonoidHom.add_apply, hY, AddMonoidHom.zero_apply, add_zero, map_add,
    AddMonoidHom.add_apply, hT, AddMonoidHom.zero_apply, add_zero]
  exact exteriorProductDedekindChow_cap_comm C _ sX sZ w (1 - p) p q _ c c' (by ring)
    (isExteriorProductOverBase_of_bivariantCapZeroDimensionalLocus_eq_zero
      sX p hS c hc)
    (bivariantCommuteOverBase_of_isDedekindChowBase_general C sX p hS sZ w q c c') t m _ _ β

end Main

end Stacks.Chow

end
